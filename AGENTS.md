# Agent Notes

## Project Overview

This is a Lean 4 project managed by Lake. Reusable modules and the CLI
entry point live under `LeanSorting/`.

The project is pinned by `lean-toolchain` to `leanprover/lean4:v4.33.0`.

## Common Commands

- Build everything with `lake build`.
- Build the library modules with `lake build LeanSorting`.
- Run the executable with `lake exe lean-sorting`.

## Lean Conventions

- Keep command entrypoint logic in `LeanSorting/App.lean`.
- Prefer small theorem statements near the definitions they justify.
- Avoid leaving `sorry` in committed code.
- Use Lake and the pinned toolchain instead of invoking a different local
  Lean version directly.

## Repository Hygiene

- Do not commit `.lake/` build artifacts.
- Preserve user proof work and local theorem experiments unless explicitly
  asked to remove them.
