# Universes as neurons

The network level of `brain/` applied to the repository's own map. Each program (field) in the centre is a node, a universe. A directed edge A -> B means a record of A cites evidence that lives in B. The same quantities as for neurons are computed exactly: connectivity, critical connections, directed cliques, and Betti numbers of the directed flag complex. Run: `python3 -I center.py && python3 -I universes/network.py`.

## First run (2026-11-25)

- 17 universes, only **3 connections**. **14 universes are isolated**: no record in one field cites evidence in another.
- The one loop (Betti number 1 in dimension 1) runs through circuits, asteroid and compute.
- circuits -> compute is the one critical connection.

## What it shows

The cross-field joins the project is about (neuron growth and phylogenetics; the knot in philosophy and DNA; the modal levels and history) are real, but they live in prose, frames and level files, not in evidence links. Measured this way, the map is a set of separate universes. That is the precise version of the tractability problem: the buses have no roads between universes.

## Open

1. Record each checked join as a finding whose evidence names files in both fields, so it becomes an edge here.
2. Count the matcher's matches and level-file arrows as a second, "proposed" layer, and compare the two graphs.
3. Then rerun: the target is one connected map with no critical connection (the rhizome condition from `philosophy/rhizome.py`).
