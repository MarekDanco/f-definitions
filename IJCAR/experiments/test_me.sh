VERBOSE=false
while getopts "v" opt; do
  case $opt in
    v) VERBOSE=true ;;
    *) echo "Usage: $0 [-v]"; exit 1 ;;
  esac
done

supports_colors() {
    case "$TERM" in
        dumb|"") return 1 ;;
        *) return 0 ;;
    esac
}

if supports_colors; then
   GREEN="\033[0;32m"
   RED="\033[0;31m"
   NC="\033[0m"
else
   GREEN=""
   RED=""
   NC=""
fi

setup_venv() {
    if [[ -d "venv" ]]; then
        echo "Found existing venv. Activating..."
    else
        echo "No venv found. Creating a new one..."
        python3 -m venv venv || return 1
        venv/bin/pip install --upgrade pip
        venv/bin/pip install z3-solver
    fi
    source venv/bin/activate || return 1
}

run() {
    local program="$1"
    local arg="$2"
    local file="$3"

    echo -n "$file: "

    if "$program" $arg "$file" >/dev/null 2>/dev/null; then
        echo -e "${GREEN}success${NC}"
    else
        echo -e "${RED}failure${NC}"
    fi
}

setup_venv

for f in smt2_benchmarks/*.smt2; do
  if [ "$VERBOSE" = true ]; then
      echo "$f"
      ./alg.py "$f"
      echo
  else
      run ./alg.py "" "$f"
  fi
done
