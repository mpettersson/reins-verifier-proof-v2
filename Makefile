
all:
	$(MAKE) -C Model
	$(MAKE) -C REINS
	$(MAKE) -C Test

clean: 
	rm Model/*.vo
	rm Model/*.v.d
	rm Model/*.glob
	rm REINS/*.vo
	rm REINS/*.v.d
	rm REINS/*.glob
