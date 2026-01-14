#!/bin/zsh

# --- Configuration ---
TIMEOUT_SEC=10
CMD_PREFIX="stack exec llang-exe -- --file examples/ski.llang --doctrine SKI --lang lambda"

# Formatting
BOLD="\033[1m"
GREEN="\033[32m"
RED="\033[31m"
GRAY="\033[90m"
RESET="\033[0m"

# --- Helper Terms (Church Encodings) ---
# We use single quotes '' so backslashes are literal.
# Use a single backslash for lambda variables so the term matches CLI expectations.
ID='(\x. x)'
ZERO='(\f. \x. x)'
ONE='(\f. \x. f x)'
TWO='(\f. \x. f (f x))'
THREE='(\f. \x. f (f (f x)))'

# Operations
PLUS='(\m. \n. \f. \x. m f (n f x))'
MUL='(\m. \n. \f. m (n f))'
POW='(\m. \n. n m)' 

# --- The Test Runner ---
print_header() {
    printf "${BOLD}%-25s %-15s %-15s %-10s${RESET}\n" "Test Name" "Complexity" "Time (sec)" "Status"
    echo "-------------------------------------------------------------------"
}

run_test() {
    local name=$1
    local complexity=$2
    local fuel=$3
    local term=$4

    # Apply arguments a and b
    local full_term="$term a b"
    
    # 1. Build the Execution Array
    # Split the prefix string into an array safely
    local -a full_cmd
    full_cmd=(${=CMD_PREFIX}) 
    # Add flags and the term as distinct arguments
    full_cmd+=(--fuel "$fuel" --term "$full_term")

    # 2. Build the Log String (for user copy-paste)
    # We manually reconstruct the command string, wrapping the term in quotes
    local log_cmd="${CMD_PREFIX} --fuel $fuel --term \"$full_term\""

    # Reset timer
    typeset -F SECONDS=0

    # 3. Execute
    # We use "${full_cmd[@]}" to ensure the term is passed as a SINGLE argument
    # protecting the spaces and backslashes inside it.
    perl -e 'alarm shift; exec @ARGV' "$TIMEOUT_SEC" \
        "${full_cmd[@]}" > /dev/null 2>&1
    
    local exit_code=$?
    local duration=$SECONDS

    if [ $exit_code -eq 0 ]; then
        printf "%-25s %-15s ${GREEN}%-15.4f${RESET} ${GREEN}PASS${RESET}\n" "$name" "$complexity" "$duration"
    elif [ $exit_code -eq 142 ]; then
        printf "%-25s %-15s ${RED}> %-13s${RESET} ${RED}TIMEOUT${RESET}\n" "$name" "$complexity" "${TIMEOUT_SEC}s"
    else
        printf "%-25s %-15s ${RED}%-15.4f${RESET} ${RED}FAIL ($exit_code)${RESET}\n" "$name" "$complexity" "$duration"
    fi
    echo "" 
}

# --- Execution ---

echo "${BOLD}Starting SKI Efficiency Stress Test${RESET}"
echo "Timeout set to: ${TIMEOUT_SEC}s per test"
echo "Output suppressed to isolate computation time.\n"

print_header

run_test "Identity" "O(1)" 50 "$ID"
run_test "Church 1" "Small" 100 "$ONE"
run_test "Church 2" "Small" 100 "$TWO"
run_test "Add 1+2" "Medium" 200 "$PLUS $ONE $TWO"
run_test "Mul 2*2" "Medium+" 500 "$MUL $TWO $TWO"
run_test "Mul 2*3" "Large" 1000 "$MUL $TWO $THREE"
run_test "Pow 2^2" "Large+" 2000 "$POW $TWO $TWO"
run_test "Pow 3^2" "Massive" 5000 "$POW $THREE $TWO"
run_test "Pow 2^3" "Massive+" 8000 "$POW $TWO $THREE"
run_test "Pow 3^3" "Huge" 10000 "$POW $THREE $THREE"
