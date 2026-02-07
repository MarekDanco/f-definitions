import pandas as pd
from pathlib import Path

C_MAP = {
    "bench_600_40000": 1,
    "bench100_2000_40000": 2,
    "bench1000_2000_40000": 3,
    "bench10000_2000_40000": 4,
    "bench100000_2000_40000": 5,
}

def parse_tab(path, solver, c):
    rows = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or ";" not in line:
                continue

            parts = [p.strip() for p in line.split(";")]
            bench_path = parts[0]
            time_part = parts[1]
            status_part = parts[2]

            benchmark = Path(bench_path).stem

            time_tokens = time_part.split()
            time_s = int(time_tokens[0])

            if "s sat" in status_part:
                status = "sat"
            elif time_s >= 1800:
                status = "timeout"
            else:
                status = "unknown"

            rows.append({
                "c": c,
                "solver": solver,
                "benchmark": benchmark,
                "time_s": time_s,
                "status": status
            })
    return rows

base = Path("tables")
rows = []

for folder, c in C_MAP.items():
    for solver in ["cvc5", "z3"]:
        tab_file = base / folder / f"{solver}.tab"
        rows.extend(parse_tab(tab_file, solver, c))

df = pd.DataFrame(rows)
print(df[df["c"] == 5])
