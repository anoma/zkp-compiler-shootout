bench:
	cd ./shootout/; cargo bench --features $(arg)

table:
	cd ./shootout/; \
	cargo criterion --features $(arg) --message-format=json | criterion-table > ../BENCHMARKS.md

all:
	cd ./shootout/; \
	cargo criterion --features "all" --message-format=json | criterion-table > ../BENCHMARKS.md
