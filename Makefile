bench:
	cd ./shootout/; cargo bench

table:
	cd ./shootout/; \
	cargo criterion --message-format=json | criterion-table > ../BENCHMARKS.md
