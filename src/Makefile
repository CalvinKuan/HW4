# ===============================
# Makefile for CS6135 Global Router (A*)
# ===============================

CXX := g++
CXXFLAGS := -O3 -march=native -DNDEBUG -flto \
            -funroll-loops -fomit-frame-pointer -ffast-math \
            -std=c++17

BIN_DIR := ../bin
OUT_DIR := ../output
SRC := hw4.cpp
TARGET := $(BIN_DIR)/router

.PHONY: all clean run run1 run2 run3 run4

# -------------------------------
# Default build rule
# -------------------------------
all: $(TARGET)

$(TARGET): $(SRC)
	@mkdir -p $(BIN_DIR)
	$(CXX) $(CXXFLAGS) $< -o $@
	@echo "✔ Build complete: $(TARGET)"

# -------------------------------
# Clean
# -------------------------------
clean:
	@rm -f $(TARGET)
	@echo "✔ Cleaned executable"

# -------------------------------
# Run single testcase
# 使用方式：
#   make run IN=xxx.txt OUT=yyy.out
# -------------------------------
run: $(TARGET)
	@mkdir -p $(OUT_DIR)
	@echo "▶ Running $(IN)"
	@$(TARGET) $(IN) $(OUT)
	@echo "✔ Output written to $(OUT)"

# -------------------------------
# Preset public testcases
# -------------------------------
run1: $(TARGET)
	@mkdir -p $(OUT_DIR)
	@$(TARGET) ../testcase/public1.txt $(OUT_DIR)/public1.out

run2: $(TARGET)
	@mkdir -p $(OUT_DIR)
	@$(TARGET) ../testcase/public2.txt $(OUT_DIR)/public2.out

run3: $(TARGET)
	@mkdir -p $(OUT_DIR)
	@$(TARGET) ../testcase/public3.txt $(OUT_DIR)/public3.out

run4: $(TARGET)
	@mkdir -p $(OUT_DIR)
	@$(TARGET) ../testcase/public4.txt $(OUT_DIR)/public4.out
run_all: $(TARGET)
	@mkdir -p $(OUT_DIR)
	@echo "▶ Running testcase1"
	@$(TARGET) ../testcase/public1.txt $(OUT_DIR)/public1.out
	@echo "▶ Running testcase2"
	@$(TARGET) ../testcase/public2.txt $(OUT_DIR)/public2.out
	@echo "▶ Running testcase3"
	@$(TARGET) ../testcase/public3.txt $(OUT_DIR)/public3.out
	@echo "▶ Running testcase4"
	@$(TARGET) ../testcase/public4.txt $(OUT_DIR)/public4.out
	@echo "===== ALL DONE ====="

