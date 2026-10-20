CC       ?= gcc
CFLAGS   ?= -std=c11 -O2 -Wall -Wextra -pedantic
TARGET   := logic_assignment
SOURCE   := src/logic_assignment.c
DOXYFILE := Doxyfile

.PHONY: all docs clean

all: $(TARGET)

$(TARGET): $(SOURCE)
	$(CC) $(CFLAGS) $(SOURCE) -o $(TARGET)

docs:
	@if command -v doxygen >/dev/null 2>&1; then \
		doxygen $(DOXYFILE); \
	else \
		echo "Doxygen is not installed. Install it, then run 'make docs' again."; \
		exit 1; \
	fi

clean:
	rm -f $(TARGET)
	rm -rf docs/api/html
