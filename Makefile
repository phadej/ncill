html : src/NCILL.agda
	agda --html src/NCILL/README.agda
	cp html/NCILL.README.html html/index.html

clean :
	find . -name '*.~' -o -name '*.agdai' | xargs rm
