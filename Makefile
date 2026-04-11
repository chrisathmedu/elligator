.PHONY: lint lint-style lint-all

lint:
	lake lint

lint-style:
	lake exe lint-style

lint-all: lint lint-style

