package main

import (
	"crypto/md5"
	"fmt"
	"io"
	"os"

	"github.com/orcastor/xdelta"
)

func checkFileSame(srcfile, tgtfile string) bool {
	if _, err := os.Stat(srcfile); os.IsNotExist(err) {
		return false
	}

	if _, err := os.Stat(tgtfile); os.IsNotExist(err) {
		return false
	}

	return getFileDigest(srcfile) == getFileDigest(tgtfile)
}

func getFileDigest(path string) string {
	file, err := os.Open(path)
	if err != nil {
		return ""
	}
	defer file.Close()

	hash := md5.New()
	if _, err := io.Copy(hash, file); err != nil {
		return ""
	}
	return fmt.Sprintf("%0x", hash.Sum(nil))
}

func main() {
	if len(os.Args) != 4 {
		os.Exit(-1)
	}

	srcfile := os.Args[2]
	tgtfile := os.Args[3]
	mode := os.Args[1]

	var err error
	switch mode {
	//case "m": // 多轮
	//	err = multipleRound(srcfile, tgtfile)
	case "s": // 单轮
		err = xdelta.SingleRound(srcfile, tgtfile)
	//case "i": // 就地生成，隐含单轮
	//	err = singleRoundInplace(srcfile, tgtfile)
	default:
		os.Exit(0)
	}

	if err != nil {
		fmt.Println(err)
	}

	if checkFileSame(srcfile, tgtfile) {
		fmt.Printf("file %s is same with %s.\n", srcfile, tgtfile)
	} else {
		fmt.Printf("file %s is different with %s.\n", srcfile, tgtfile)
	}
}
