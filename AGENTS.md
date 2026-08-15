# Agent Notes

## Project Overview

This is a Lean 4 project managed by Lake. The library entry point is
`LeanStuff.lean`, the executable entry point is `Main.lean`, and reusable
modules live under `LeanStuff/`.

The project is pinned by `lean-toolchain` to `leanprover/lean4:v4.33.0`.

## Common Commands

- Build everything with `lake build`.
- Build the library with `lake build LeanStuff`.
- Run the executable with `lake exe lean-stuff`.

## Lean Conventions

- Keep public imports collected in `LeanStuff.lean`.
- Prefer small theorem statements near the definitions they justify.
- Avoid leaving `sorry` in committed code.
- Use Lake and the pinned toolchain instead of invoking a different local
  Lean version directly.

## Repository Hygiene

- Do not commit `.lake/` build artifacts.
- Preserve user proof work and local theorem experiments unless explicitly
  asked to remove them.
