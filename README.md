# Formal Verification of Shortest Path Algorithms in Lean

This repository contains my final year project formalising parts of shortest-path theory in Lean 4, specifically the Floyd-Warshall algorithm.

## Project Overview

The project defines finite weighted graphs, paths, path weights, and proves correctness properties for a formal model of Floyd-Warshall.

The main result is a correctness theorem showing that the Floyd-Warshall recurrence computed shortest path distances over a resticted set of intermediate vertices:

distUpToList G (k :: ks) i j = 
    min (distUpToList G ks i j)
        (distUpToList G ks i k + distUpToList G ks k j)

## Building the project:
Build using Lake:
```bash
lake build
```

If this is your first time building the project, dependencies may need to be downloaded:
```bash
lake build -R
```

## Notes
- The formalisation focuses on mathematica correctness rather than execution.
- Some definitions are marked ```noncomputable```.
- The development assumes non-negative edge weights and does not explicitly handle negative cycles.
