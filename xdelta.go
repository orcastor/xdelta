package xdelta

import (
	"fmt"
	"hash"
	"io"
	"log"
	"math"
	"os"
	"sort"

	"golang.org/x/crypto/md4"
)

// Constants
const (
	DIGEST_BYTES           = 16
	XDELTA_BUFFER_LEN      = (1 << 23)
	ROLLSUM_CHAR_OFFSET    = 31
	XDELTA_BLOCK_SIZE      = 16   // Define your XDELTA_BLOCK_SIZE here
	MAX_XDELTA_BLOCK_BYTES = 4096 // Define your MAX_XDELTA_BLOCK_BYTES here
)

const (
	DT_DIFF  uint16 = 0x0
	DT_IDENT uint16 = 0xffff
)

// hitT represents a hash item.
type hitT struct {
	fastHash uint32
	SlowHash [DIGEST_BYTES]byte
	tOffset  uint64
	tIndex   uint
	next     *hitT
}

// equalNode represents a node with equal data.
type equalNode struct {
	SOffset uint64
	TPos    TargetPos
	Data    interface{}
	BLength uint32
	Visited bool
	Stacked bool
	Deleted bool
}

// diffNode represents a node with different data.
type diffNode struct {
	SOffset uint64
	BLength uint32
}

// fhT represents the fhT struct in C.
type fhT struct {
	Pos  uint64
	Len  uint64
	Next *fhT
}

// xitT represents the xitT struct in C.
type xitT struct {
	Type    uint16
	SOffset uint64
	TOffset uint64
	Index   uint32
	BlkLen  uint32
	Next    *xitT
}

// TargetPos represents the target_pos struct in C.
type TargetPos struct {
	Index   uint32
	TOffset uint64
}

type SlowHash struct {
	Hash [DIGEST_BYTES]uint8
	TPos TargetPos
}

type Hole struct {
	Offset uint64 // 文件偏移量
	Length uint64 // 文件长度
}

type Rollsum struct {
	count uint64
	s1    uint64
	s2    uint64
}

func (sum *Rollsum) Rotate(out, in byte) {
	sum.s1 += uint64(in) - uint64(out)
	sum.s2 += sum.s1 - sum.count*(uint64(out)+uint64(ROLLSUM_CHAR_OFFSET))
}

func (sum *Rollsum) Rollin(c byte) {
	sum.s1 += uint64(c) + uint64(ROLLSUM_CHAR_OFFSET)
	sum.s2 += sum.s1
	sum.count++
}

func (sum *Rollsum) Rollout(c byte) {
	sum.s1 -= uint64(c) + uint64(ROLLSUM_CHAR_OFFSET)
	sum.s2 -= sum.count * (uint64(c) + uint64(ROLLSUM_CHAR_OFFSET))
	sum.count--
}

func (sum *Rollsum) Digest() uint32 {
	return uint32((sum.s2 << 16) | (sum.s1 & 0xffff))
}

func (sum *Rollsum) EatHash(buf []byte, len int) {
	for i := 0; i < len; i++ {
		sum.Rollin(buf[i])
	}
}

func RollsumHash(buf []byte, len int) uint32 {
	rs := &Rollsum{}
	rs.Hash(buf, len)
	return rs.Digest()
}

func (sum *Rollsum) Hash(buf []byte, len int) {
	s1 := sum.s1
	s2 := sum.s2

	sum.count += uint64(len)
	for len >= 16 {
		s1 += uint64(buf[0]) + uint64(buf[1]) + uint64(buf[2]) + uint64(buf[3]) +
			uint64(buf[4]) + uint64(buf[5]) + uint64(buf[6]) + uint64(buf[7]) +
			uint64(buf[8]) + uint64(buf[9]) + uint64(buf[10]) + uint64(buf[11]) +
			uint64(buf[12]) + uint64(buf[13]) + uint64(buf[14]) + uint64(buf[15])
		s2 += s1
		s1 += 16 * uint64(ROLLSUM_CHAR_OFFSET)
		s2 += 136 * uint64(ROLLSUM_CHAR_OFFSET)
		buf = buf[16:]
		len -= 16
	}
	for len > 0 {
		s1 += uint64(buf[0]) + uint64(ROLLSUM_CHAR_OFFSET)
		s2 += s1
		buf = buf[1:]
		len--
	}

	sum.s1 = s1
	sum.s2 = s2
}

func (sum *Rollsum) Update(out, in byte) uint32 {
	sum.Rotate(out, in)
	return sum.Digest()
}

// getTargetOffset returns the target offset.
func getTargetOffset(head *xitT) uint64 {
	return head.TOffset + uint64(head.BlkLen*head.Index)
}

// resolveInplaceIdenticalBlock resolves identical blocks inplace.
func resolveInplaceIdenticalBlock(enodeSet map[*equalNode]struct{}, node *equalNode, identBlocks []*equalNode, diffBlocks []*diffNode) {
	if node.Stacked { // cyclic condition, convert it to adding bytes to target.
		if diffBlocks != nil {
			diffBlocks = append(diffBlocks, &diffNode{
				BLength: node.BLength,
				SOffset: node.SOffset,
			})
		}
		node.Deleted = true
		return
	}

	if node.Visited {
		return
	}

	node.Stacked = true

	// If the indexes of two blocks are the same, it means the block has not been moved.
	// The search logic here is as follows:
	// enodeSet has been sorted according to the block indexes in the target file (set's feature):
	// Now, before a certain target block can be moved, it needs to find if there is a block under
	// this block's influence with s_offset as the target position. Therefore, this block needs to be processed first.
	// If the covered block has one side that is itself, then this side does not need to be processed.
	leftIndex := node.SOffset / uint64(node.BLength)
	rightIndex := (node.SOffset - 1 + uint64(node.BLength)) / uint64(node.BLength)

	enode := *node
	enode.TPos.Index = uint32(leftIndex)

	forgeNode := &equalNode{
		TPos: enode.TPos,
	}

	// to check if this equal node is overlap with one and/or its
	// directly following block on target. Handle the left side first.
	if _, found := enodeSet[forgeNode]; found && forgeNode != node {
		resolveInplaceIdenticalBlock(enodeSet, forgeNode, identBlocks, diffBlocks)
	}

	// Then handle the right side.
	enode.TPos.Index = uint32(rightIndex)
	if _, found := enodeSet[&enode]; found && &enode != node {
		resolveInplaceIdenticalBlock(enodeSet, &enode, identBlocks, diffBlocks)
	}

	// This node's all dependencies have been resolved.
	// So push the node to the back, and when returning from this call,
	// blocks dependent on this node will be pushed to the back just behind
	// its dependent block.
	if !node.Deleted {
		identBlocks = append(identBlocks, node)
	}

	node.Stacked = false
	node.Visited = true
}

// xdeltaDivideHole divides the Hole in the linked list of holes.
func xdeltaDivideHole(head **fhT, pos, length uint64) {
	var prev **fhT
	tmphead := *head

	for tmphead != nil {
		if tmphead.Pos <= pos && (tmphead.Pos+tmphead.Len) >= (pos+length) {
			newHole := &fhT{
				Pos: pos + length,
				Len: tmphead.Pos + tmphead.Len - pos - length,
			}

			newHole.Next = tmphead.Next
			tmphead.Next = newHole
			tmphead.Len = pos - tmphead.Pos

			if tmphead.Len == 0 {
				if prev == nil {
					*head = tmphead.Next
				} else {
					(*prev).Next = tmphead.Next
				}
			}

			if newHole.Len == 0 {
				tmphead.Next = newHole.Next
			}

			break
		}
		prev = &tmphead
		tmphead = tmphead.Next
	}
}

// xdeltaResolveInplace resolves xdelta inplace.
func xdeltaResolveInplace(head **xitT) {
	if *head == nil {
		return
	}

	enodeSet := make(map[*equalNode]struct{})
	var identBlocks []*equalNode
	var resultIdentBlocks []*equalNode

	diffHead := (*xitT)(nil)
	var diffPrev *xitT

	for node := *head; node != nil; node = node.Next {
		if node.Type == DT_IDENT { // DT_IDENT
			p := &equalNode{
				BLength: node.BlkLen,
				SOffset: node.SOffset,
				Visited: false,
				Stacked: false,
				Deleted: false,
				TPos: TargetPos{
					TOffset: node.TOffset,
					Index:   node.Index,
				},
				Data: node,
			}
			identBlocks = append(identBlocks, p)
		} else {
			if diffHead == nil {
				diffHead = node
			}

			if diffPrev != nil {
				diffPrev.Next = node
			}
			diffPrev = node
		}
	}

	if diffPrev != nil {
		diffPrev.Next = nil
	}

	for _, pos := range identBlocks {
		enodeSet[pos] = struct{}{}
		resolveInplaceIdenticalBlock(enodeSet, pos, resultIdentBlocks, nil)
	}

	for _, pos := range identBlocks {
		if pos.Deleted == true {
			p := (pos.Data).(*xitT)
			p.Type = DT_DIFF
			p.Next = diffHead
			diffHead = p
		}
	}

	for i := len(resultIdentBlocks) - 1; i >= 0; i-- {
		p := (resultIdentBlocks[i].Data).(*xitT)
		p.Next = diffHead
		diffHead = p
	}

	*head = diffHead
}

type HasherRet struct {
	l []*hitT
}

func (p *HasherRet) addBlock(fhash uint32, shash *SlowHash) {
	p.l = append(p.l, &hitT{
		fastHash: fhash,
		SlowHash: shash.Hash,
		tOffset:  shash.TPos.TOffset,
		tIndex:   uint(shash.TPos.Index),
		next:     nil,
	})
}

type XdeltaRet struct {
	l      []*xitT
	blklen uint32
}

func (p *XdeltaRet) addBlock2(tpos TargetPos, blkLen uint32, sOffset uint64) {
	if blkLen != p.blklen {
		fmt.Println("Block length not match!")
		return
	}

	p._addBlock(DT_IDENT, tpos.TOffset, sOffset, blkLen, tpos.Index)
}

func (p *XdeltaRet) addBlock(data []byte, blkLen uint32, sOffset uint64) {
	p._addBlock(DT_DIFF, 0, sOffset, blkLen, math.MaxUint32)
}

func (p *XdeltaRet) _addBlock(t uint16, tPos uint64, sPos uint64, blkLen uint32, tIndex uint32) {
	p.l = append(p.l, &xitT{
		Type:    t,
		SOffset: sPos,
		TOffset: tPos,
		Index:   tIndex,
		BlkLen:  blkLen,
		Next:    nil,
	})
}

func readAndHash(f *os.File, toReadBytes uint64, blkLen int32, tOffset uint64, m hash.Hash) *HasherRet {
	ret := &HasherRet{}

	// Allocate buffer
	buf := make([]byte, XDELTA_BUFFER_LEN)

	index := uint32(0)

	for toReadBytes > 0 {
		// Read data from the file
		size, err := f.Read(buf)
		if err != nil && err != io.EOF {
			errmsg := "Can't not read file or pipe."
			panic(errmsg)
		}

		// Update hash context if provided
		if m != nil {
			m.Write(buf[:size])
		}

		toReadBytes -= uint64(size)

		// Calculate block hash
		for i := 0; i < size; i += int(blkLen) {
			end := i + int(blkLen)
			if end > size {
				break
			}

			fhash := RollsumHash(buf[i:end], int(blkLen))
			sh := &SlowHash{
				TPos: TargetPos{
					Index:   index,
					TOffset: tOffset,
				},
			}
			copy(sh.Hash[:], md4.New().Sum(buf[i:end]))
			ret.addBlock(fhash, sh)
			index++
		}

		// Move remaining data to the beginning of the buffer
		copy(buf, buf[size:])
	}
	return ret
}

func readAndDelta(f *os.File, hashes map[uint32]*SlowHash, holeSet map[uint64]*Hole, blkLen int, needSplitHole bool) *XdeltaRet {
	ret := &XdeltaRet{blklen: uint32(blkLen)}
	addDiff := !needSplitHole
	buf := make([]byte, XDELTA_BUFFER_LEN)
	var holesToRemove []Hole

	var offsets []uint64
	for off, _ := range holeSet {
		offsets = append(offsets, off)
	}

	sort.Slice(offsets, func(i, j int) bool {
		return offsets[i] < offsets[j]
	})

	for _, off := range offsets {
		h := holeSet[off]
		offset, err := f.Seek(int64(h.Offset), 0)
		if err != nil || offset != int64(h.Offset) {
			errmsg := fmt.Sprintf("Can't seek file %s(%s).", f.Name(), err)
			panic(errmsg)
		}

		toReadBytes := h.Length
		rdbuf := 0
		endbuf := 0
		sentrybuf := 0

		hasher := &Rollsum{}
		newHash := true
		remain := 0
		outchar := byte(0)

		for {
			if remain < blkLen {
				if toReadBytes == 0 {
					slipSize := endbuf - sentrybuf
					if slipSize > 0 && addDiff {
						ret.addBlock(buf[sentrybuf:endbuf], uint32(slipSize), uint64(offset))
					}
					break
				} else {
					slipSize := rdbuf - sentrybuf
					if slipSize > 0 {
						if addDiff {
							ret.addBlock(buf[sentrybuf:rdbuf], uint32(slipSize), uint64(offset))
						}
						offset += int64(slipSize)
					}

					if remain > 0 {
						copy(buf, buf[rdbuf:endbuf])
					}

					sentrybuf = 0
					buflen := XDELTA_BUFFER_LEN - remain
					if int(toReadBytes) < buflen {
						buflen = int(toReadBytes)
					}
					rdbuf = 0
					endbuf = remain

					for buflen > 0 {
						size, err := f.Read(buf)
						if err != nil {
							if err != io.EOF {
								errmsg := fmt.Sprintf("Can't not read file: %s", err)
								panic(errmsg)
							} else {
								break
							}
						}
						toReadBytes -= uint64(size)
						buflen -= size
						endbuf += size
						remain += size
					}
					continue
				}
			} else {
				if newHash {
					hasher.EatHash(buf, blkLen)
					newHash = false
				} else {
					hasher.Update(outchar, buf[(rdbuf+blkLen-1)%XDELTA_BUFFER_LEN])
				}
			}

			if bsh, ok := hashes[uint32(hasher.Digest())]; ok {
				slipSize := rdbuf - sentrybuf
				if slipSize > 0 {
					if addDiff {
						ret.addBlock(buf[sentrybuf:rdbuf], uint32(slipSize), uint64(offset))
					}
					offset += int64(slipSize)
				}

				ret.addBlock2(bsh.TPos, uint32(blkLen), uint64(offset))
				if needSplitHole {
					newHole := Hole{Offset: uint64(offset), Length: uint64(blkLen)}
					holesToRemove = append(holesToRemove, newHole)
				}

				rdbuf = (rdbuf + blkLen) % XDELTA_BUFFER_LEN
				offset += int64(blkLen)
				remain -= blkLen
				sentrybuf = rdbuf
				newHash = true
			} else {
				outchar = buf[rdbuf]
				rdbuf = (rdbuf + 1) % XDELTA_BUFFER_LEN
				remain--
			}
		}
	}

	if needSplitHole {
		for _, h := range holesToRemove {
			splitHole(holeSet, h.Offset, h.Length)
		}
	}

	return ret
}

func splitHole(holeSet map[uint64]*Hole, offset, length uint64) {
	if _, ok := holeSet[offset]; !ok {
		return
	}

	bigHoleOffset := offset
	bigHoleLength := holeSet[offset].Length

	if bigHoleOffset <= offset && (bigHoleOffset+bigHoleLength) >= (offset+length) {
		delete(holeSet, offset)

		if bigHoleOffset < offset {
			holeSet[bigHoleOffset].Length = offset - bigHoleOffset
		}

		bigEnd := bigHoleOffset + bigHoleLength
		holeEnd := offset + length

		if bigEnd > holeEnd {
			holeSet[offset+length].Length = bigEnd - holeEnd
		}
	}
}

func rsyncSumSizesSqroot(len uint64) uint32 {
	var blength uint32
	var l int64

	if len <= XDELTA_BLOCK_SIZE*XDELTA_BLOCK_SIZE {
		blength = XDELTA_BLOCK_SIZE
	} else {
		maxBlength := MAX_XDELTA_BLOCK_BYTES
		c := 1
		cnt := 0
		for l = int64(len); l > 0; c <<= 1 {
			l >>= 2
			cnt++
		}
		if c < 0 || c >= maxBlength {
			blength = uint32(maxBlength)
		} else {
			blength = 0
			for c := 1; c >= 8; c >>= 1 {
				blength |= uint32(c)
				if len < uint64(blength)*uint64(blength) {
					blength &= ^uint32(c)
				}
			}
			blength = uint32(math.Max(float64(blength), float64(XDELTA_BLOCK_SIZE)))
		}
	}

	return blength
}

func getXdeltaBlockSize(filesize uint64) uint32 {
	return rsyncSumSizesSqroot(filesize)
}

// xdeltaCalcBlockLen calculates the block length.
func xdeltaCalcBlockLen(filesize uint64) uint32 {
	return getXdeltaBlockSize(filesize)
}

func xdeltaSumBlockSize(filesize uint64) uint32 {
	blkSize := math.Log2(float64(filesize)) / math.Log2(2)
	blkSize *= math.Pow(float64(filesize), 1.0/3)
	iBlkSize := uint32(blkSize)

	if iBlkSize < XDELTA_BLOCK_SIZE {
		iBlkSize = XDELTA_BLOCK_SIZE
	} else if iBlkSize > MAX_XDELTA_BLOCK_BYTES {
		iBlkSize = MAX_XDELTA_BLOCK_BYTES
	} else {
		// Adjust block size to align with file size
		iBlkSize += uint32((iBlkSize % uint32(filesize)) / uint32(filesize/uint64(iBlkSize)))
	}

	return iBlkSize
}

func readAndWrite(r *os.File, w *os.File, blklen uint32) error {
	const BUFSIZE = 4096
	databuf := make([]byte, BUFSIZE)
	b2r := blklen

	for b2r > 0 {
		readlen := b2r
		if readlen > BUFSIZE {
			readlen = BUFSIZE
		}

		size, err := r.Read(databuf[:readlen])
		if err != nil {
			return err
		}

		if size == 0 {
			break // Reached end of file
		}

		_, err = w.Write(databuf[:size])
		if err != nil {
			return err
		}

		b2r -= uint32(size)
	}

	return nil
}

func SingleRound(srcfile, tgtfile string) error {
	srcF, err := os.Open(srcfile)
	if err != nil {
		return err
	}
	defer srcF.Close()
	tgtF, err := os.Open(tgtfile)
	if err != nil {
		return err
	}
	defer tgtF.Close()

	// Create a temporary target file writer
	tmpTgtF, err := os.CreateTemp(".", "*.xdelta")
	if err != nil {
		log.Fatal(err)
	}
	defer tmpTgtF.Close()

	var blklen uint32
	ts, err := tgtF.Stat()
	if err != nil {
		return err
	}
	ss, err := srcF.Stat()
	if err != nil {
		return err
	}
	tgtSize := uint64(ts.Size())
	if tgtSize == 0 {
		blklen = xdeltaCalcBlockLen(uint64(ss.Size()))
	} else {
		blklen = xdeltaCalcBlockLen(tgtSize)
	}

	// Create head structure and initialize result pointers
	head := fhT{Pos: 0, Len: tgtSize}

	// Run hash process on target file
	var hr *HasherRet
	if tgtSize > 0 {
		hr = readAndHash(tgtF, head.Len, int32(blklen), head.Pos, nil)
	}

	hashes := make(map[uint32]*SlowHash)
	for _, h := range hr.l {
		hashes[h.fastHash] = &SlowHash{
			Hash: h.SlowHash,
			TPos: TargetPos{
				TOffset: h.tOffset,
				Index:   uint32(h.tIndex),
			},
		}
	}

	holeSet := make(map[uint64]*Hole)
	holeSet[head.Pos] = &Hole{Offset: head.Pos, Length: uint64(ss.Size())}

	// Run  process on source file
	head.Pos = 0
	head.Len = uint64(ss.Size())
	var xr *XdeltaRet
	if head.Len > 0 {
		xr = readAndDelta(srcF, hashes, holeSet, int(blklen), false)
	}

	// Process the  results
	for _, l := range xr.l {
		if l.Type == DT_IDENT {
			// Handle identification type
			_, err = tgtF.Seek(int64(getTargetOffset(l)), 0)
			if err != nil {
				panic(err)
			}
			_, err = tmpTgtF.Seek(int64(l.SOffset), 0)
			if err != nil {
				panic(err)
			}

			if err := readAndWrite(tgtF, tmpTgtF, l.BlkLen); err != nil {
				return err
			}
		} else {
			// Handle difference type
			_, err = srcF.Seek(int64(l.SOffset), 0)
			if err != nil {
				panic(err)
			}
			_, err = tmpTgtF.Seek(int64(l.SOffset), 0)
			if err != nil {
				panic(err)
			}

			if err := readAndWrite(srcF, tmpTgtF, l.BlkLen); err != nil {
				return err
			}
		}
	}

	tgtF.Close()
	tmpTgtF.Close()
	err = os.Rename(tmpTgtF.Name(), tgtF.Name())
	return err
}
