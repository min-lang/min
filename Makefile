two: one
	/usr/bin/time ./min1 binary `cat packs` 3< main.ma > min2 && [ -s min2 ] && chmod +x min2 && ./min2 fact
	[[ `md5 < min1` == `md5 < min2` ]]

one:
	sed 's= *\#.*==' packs.m > packs
	/usr/bin/time ./min binary `cat packs` 3< main.ma > min1 && [ -s min1 ] && chmod +x min1 && ./min1 fact

test: all
	./min1 test
	./min1 cocoa & sleep 1; killall min1
	./min1 httpd & sleep 1; curl localhost:8080; killall min1

race: all
	for x in `seq 1 1000`; do ./min2 fact; done

clean:
	rm -f packs min1 min2
