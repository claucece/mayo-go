TEST_FLAGS=./... -cover -count=1
BENCH_FLAGS=$(TEST_FLAGS) -bench=.
COMPILED=mayo-go
BUILD_FLAGS=-o $(COMPILED)

.PHONY: build
build:
	go build $(BUILD_FLAGS)

.PHONY: test
test:
	go test $(TEST_FLAGS)

.PHONY: bench
bench:
	go test $(BENCH_FLAGS)

.PHONY: docs
docs:
	./docs.sh
