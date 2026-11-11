# Work plan and status

## Status

The formalization is complete. The three main theorems are proved with no `sorry` and depend only
on `propext`, `Classical.choice` and `Quot.sound`:

| Blueprint | Lean | File |
|---|---|---|
| `thm:main-ergodic` (`t:CSZ`) | `CantorSzemeredi.cantor_szemeredi` | `CantorSzemeredi/Frozen/MainTheorem.lean` |
| `cor:syndetic` (`c:syndetic`) | `CantorSzemeredi.cantor_szemeredi_syndetic` | `CantorSzemeredi/Frozen/Syndetic.lean` |
| `thm:main-integers` (`t:CSZ-Integers`) | `CantorSzemeredi.cantor_szemeredi_integers` | `CantorSzemeredi/Frozen/Integers.lean` |

Every blueprint item carries `\leanok` except `lem:extensions`, which has a statement only. Every
`\lean{...}` name in the blueprint resolves to a declaration in this repository.

Verified on the merged tree: `lake build` (9129 jobs, no errors), `lake build Challenge Solution`,
and all five scripts in `scripts/` (axiom audit, frozen anchors, frozen ABI, module check,
challenge match). See `README.md` for the commands.

## How this repository was assembled

Two formalizations were merged.

1. **The partial formalization** developed here through commit `d29e8f9`: the Cantor set, measure
   preserving systems and factors, the CSZ property, the compact and weakly mixing extension
   principles, the symbolic model, Furstenberg correspondence, and the van der Waerden chapter.
   It had two `sorry`: the Furstenberg–Zimmer dichotomy (`lem:dichotomy`) and the
   `CountablyGenerated` instance in the ergodic decomposition (`lem:ergodic-decomposition`).

2. **A completion of it** that removed both. Its `Port/` tree is that same development, ported
   unchanged in its mathematics to Lean's module system under the namespace `CSZPort`, plus a
   `Proof/` tree proving the dichotomy along the Furstenberg–Zimmer route and the ergodic
   decomposition independently, and a `Frozen/` tree holding the author-approved statements.

The merge took the second as the base, since it is the superset on the main line and is verified
end to end, and carried over the parts of the first that it had left out as not needed:

- `Port/VdW/` — the Cantor-set van der Waerden theorem of §4 (`topological_vdW`, `vdW_infinite`,
  `vdW_finitary`);
- `Port/Dynamics/WMSystem.lean` — weakly mixing systems are CSZ (`cor:wm-system`,
  `cor:wm-compact-are-csz`);
- `Port/Dynamics/WienerAtoms.lean` and `Port/Dynamics/CompactRoots.lean`.

Those nine files were converted to the module system and the `CSZPort` namespace by the same
recipe as the rest of `Port/`, and each names its origin in its header.

The blueprint was kept and repointed: ported declarations moved from `CantorSzemeredi.…` to
`CSZPort.…`, and the structure and overview chapters now name the declarations in `Proof/` and
`Frozen/`. Where the Lean statement is stronger than the blueprint's, the item carries a
formalization note; see `docs/ERRATA-AND-DEVIATIONS.md`.

## Deviations worth remembering

- The reduction to ergodic systems (`prop:reduction`) is not used. The dichotomy is proved for
  every system on a standard Borel space, without ergodicity, so `csz_all` gives the conclusion
  directly. The ergodic decomposition is proved anyway. (Deviation V1.)
- The paper's definition of conditional compactness places `min_q` outside the `L^∞` norm, which
  read literally excludes standard compact extensions. The formalization uses Moreira's form.
  (Erratum E1.)

## If work resumes

- `lem:extensions` (`csz_sets_of_compactExtension`) is the one blueprint item with a statement but
  no `\leanok`; check whether the proved parts now cover it.
- The frozen statements and their hashes must not change. Anything else is ordinary work under the
  conventions in `CLAUDE.md`.
