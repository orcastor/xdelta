package xdelta

import (
	"fmt"
	"hash"
	"log"
	"math"
	"os"

	"golang.org/x/crypto/md4"
)

// Constants
const (
	DIGEST_BYTES        = 16
	XDELTA_BUFFER_LEN   = (1 << 23)
	ROLLSUM_CHAR_OFFSET = 31
)

// fh_t represents a file hole.
type fh_t struct {
	pos  uint64
	len  uint64
	next *fh_t
}

// hit_t represents a hash item.
type hit_t struct {
	fastHash uint32
	slowHash [DIGEST_BYTES]byte
	tOffset  uint64
	tIndex   uint
	next     *hit_t
}

// xdeltaItem represents an item in xdelta.
type xdeltaItem struct {
	typ     uint16
	sOffset uint64
	tOffset uint64
	index   uint
	blklen  uint
	next    *xdeltaItem
}

// equalNode represents a node with equal data.
type equalNode struct {
	SOffset uint64
	TPos    targetPos
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

// fhT represents the fh_t struct in C.
type fhT struct {
	Pos  uint64
	Len  uint64
	Next *fhT
}

// xitT represents the xit_t struct in C.
type xitT struct {
	Type    uint16
	SOffset uint64
	TOffset uint64
	Index   uint32
	BlkLen  uint32
	Next    *xitT
}

// targetPos represents the target_pos struct in C.
type targetPos struct {
	Index   uint32
	TOffset uint64
}

type slowHash struct {
	Hash [DIGEST_BYTES]uint8
	TPos targetPos
}

type hole struct {
	Offset uint64 // 文件偏移量
	Length uint64 // 文件长度
}

type Rollsum struct {
	count uint64
	s1    uint64
	s2    uint64
}

type xdeltaStream interface {
	startHashStream(fname string, blkLen int32)
	addBlock(buf []byte, blkLen uint32, sOffset uint64)
	addBlock2(tpos targetPos, blkLen uint32, sOffset uint64)
	endOneRound()
	endHashStream(filsize uint64)
	onError(errmsg string, errorno int)
	setHoles(holeset *[]hole)
}

type hasherStream interface {
	startHashStream(fname string, blkLen int32)
	addBlock(fhash uint32, shash slowHash)
	endHashStream(fileHash []uint8, filsize uint64)
	endFirstRound(fileHash []uint8) bool
	nextRound(blkLen int32)
	endOneRound()
	onError(errmsg string, errorno int)
	setHoles(holeset *[]hole)
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
func getTargetOffset(head *xdeltaItem) uint64 {
	return head.tOffset + uint64(head.blklen*head.index)
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

// xdeltaDivideHole divides the hole in the linked list of holes.
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
		if node.Type == 0 { // DT_IDENT
			p := &equalNode{
				BLength: node.BlkLen,
				SOffset: node.SOffset,
				Visited: false,
				Stacked: false,
				Deleted: false,
				TPos: targetPos{
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
			p.Type = 1 // DT_DIFF
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

func readAndHash(f *os.File, stream hasherStream, toReadBytes uint64, blkLen int32, tOffset uint64, m hash.Hash) {
	const xDeltaBufferLen = 1024 // Assuming XDELTA_BUFFER_LEN is defined as 1024 in C

	// Allocate buffer
	buf := make([]byte, xDeltaBufferLen)

	index := uint32(0)

	for toReadBytes > 0 {
		// Read data from the file
		size, err := f.Read(buf[:toReadBytes])
		if err != nil || size <= 0 {
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
			bsh := slowHash{
				TPos: targetPos{
					Index:   index,
					TOffset: tOffset,
				},
				Hash: md4.New().Sum(buf[i:end]),
			}
			stream.addBlock(fhash, bsh)
			index++
		}

		// Move remaining data to the beginning of the buffer
		copy(buf, buf[size:])
	}
}

func ReadAndDelta(f *os.File, stream xdeltaStream, hashes map[uint32]*slowHash, holeSet map[uint64]*hole, blkLen int, needSplitHole bool) {
	adddiff := !needSplitHole
	buf := make([]byte, XDELTA_BUFFER_LEN)
	var holesToRemove []hole

	for _, h := range holeSet {
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
					if slipSize > 0 && adddiff {
						stream.addBlock(buf[sentrybuf:endbuf], uint32(slipSize), uint64(offset))
					}
					break
				} else {
					slipSize := rdbuf - sentrybuf
					if slipSize > 0 {
						if adddiff {
							stream.addBlock(buf[sentrybuf:rdbuf], uint32(slipSize), uint64(offset))
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
						size, err := f.Read(buf[remain:])
						if err != nil || size <= 0 {
							errmsg := fmt.Sprintf("Can't not read file or pipe: %s", err)
							panic(errmsg)
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
					if adddiff {
						stream.addBlock(buf[sentrybuf:rdbuf], uint32(slipSize), uint64(offset))
					}
					offset += int64(slipSize)
				}

				stream.addBlock2(bsh.TPos, uint32(blkLen), uint64(offset))
				if needSplitHole {
					newHole := hole{Offset: uint64(offset), Length: uint64(blkLen)}
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
}

func splitHole(holeSet map[uint64]*hole, offset, length uint64) {
	if _, ok := holeSet[offset]; !ok {
		log.Fatal("hole does not exist")
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

		return
	}

	log.Fatal("hole must exist")
}

func rsyncSumSizesSqroot(len uint64) uint32 {
	const (
		XDELTA_BLOCK_SIZE      = 16   // Define your XDELTA_BLOCK_SIZE here
		MAX_XDELTA_BLOCK_BYTES = 4096 // Define your MAX_XDELTA_BLOCK_BYTES here
	)

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
