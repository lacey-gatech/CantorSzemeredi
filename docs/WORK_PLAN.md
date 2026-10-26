# Work plan

Status as of the handoff (git HEAD `6c9969b`, "Van der Waerden chapter formalized"). Working tree was clean. Conventions are in `CLAUDE.md`.

## Done (sorry-free, axioms checked, blueprint annotated)

- **Cantor** (`cantor.tex`): `Cantor/Enum.lean`, `Cantor/Residues.lean`, `Cantor/Defs.lean`. Includes `pow_mul_enum_add_mem`, `enum_block`, `enum_sub_enum_eq`, `card_goodResidues_ge`, `enum_zero`.
- **MPS and extensions** (`mps.tex`): `Dynamics/System.lean`, `Dynamics/Extensions.lean` (`WeaklyMixing`, `CondWeaklyMixing`, `WeaklyMixingExtension`, `MemModule`, `MemL2`, `Factor.toPow`).
- **CSZ and compact systems** (`csz.tex`, `compact.tex`): `Dynamics/CSZ.lean` (`Factor.CSZ`, `multiCorr`, `trivial_CSZ`), `Dynamics/CompactSystem.lean` (`Factor.top`, `CSZ_of_compactSystem`).
- **Weak mixing** (`weakmixing.tex`):
  - Main estimate, in `WMInduction.lean` through `WMMainFinal.lean`. Final result: `MPS.wm_extension_tendsto`.
  - `WMShift`, `WMTransfer`, `WMPair`, `WMAverage`, `WMLimit`, `WMClass`, `WMPerShift`, `WMCorr`, `WMSpectral`, `WMAverageShift`, `WMVdC`, `WMStar`.
  - Sets to functions: `MPS.cesaroTo0_L2`, `MPS.weaklyMixingExtension_of_weaklyMixing`.
  - Part (W) of the extension principles: `WMPartW.lean`, `MPS.CSZ_of_weaklyMixingExtension`.
  - `cor:wm-system`: `MPS.weaklyMixing_tendsto_prod`.
  - Weakly mixing part of `cor:wm-compact-are-csz`: `MPS.CSZ_of_weaklyMixing`.
- **Van der Waerden** (`vdw.tex`): `VdW/Digits.lean`, `VdW/Minimal.lean`, `VdW/Focus.lean`, `VdW/Cvdw.lean`, `VdW/Infinite.lean`, `VdW/Finitary.lean`. Final results: `CantorData.topological_vdW`, `vdW_infinite`, `vdW_finitary`.
- **Basic**: `CantorSzemeredi/Basic.lean` holds `syndetic_of_uniformLiminf_pos` (used by `cor:syndetic`).

## Remaining

### 1. Structure chapter (`structure.tex`), in document order

The first item is done; the rest are not started.

| Label | Lean name in blueprint | Status |
|---|---|---|
| `lem:sSup-factor` | `CantorSzemeredi.MPS.Factor.sSup` | **done** (`Structure.lean`) |
| `lem:chain-approx` | `CantorSzemeredi.MPS.Factor.exists_mem_chain_symmDiff_lt` | **done** (`Structure.lean`) |
| `lem:chain-comparison` | `CantorSzemeredi.MPS.multiCorr_ge_half_of_condExp` | not started |
| `lem:chain` | `CantorSzemeredi.MPS.CSZ_sSup_chain` | not started |
| `lem:dichotomy` | `CantorSzemeredi.MPS.weaklyMixingExtension_or_compactExtension` | not started |
| `thm:ecsz` | `CantorSzemeredi.MPS.CSZ_of_ergodic` | not started |
| `lem:symbolic-model` | `CantorSzemeredi.MPS.symbolicModel`, `CantorSzemeredi.MPS.multiCorr_symbolicModel` | not started |
| `lem:ergodic-decomposition` | `CantorSzemeredi.MPS.ergodicDecomposition` | not started |
| `lem:fatou-uniform` | `CantorSzemeredi.uniformLiminf_integral_ge` | not started |
| `prop:reduction` | `CantorSzemeredi.MPS.CSZ_of_forall_ergodic_CSZ` | not started |
| `thm:furstenberg-correspondence` | `CantorSzemeredi.furstenberg_correspondence` | not started |

Notes:
- The names above are placeholders from the blueprint. Confirm each one against the proof before writing it, and rename the blueprint entry if the final name differs.
- Before starting, check the `Dynamics/Fibre.lean` import in `CantorSzemeredi.lean`. Its role in this chapter is unknown, so read it first.
- Work through the chapter in the order listed. `lem:chain` depends on `lem:sSup-factor` and `lem:chain-approx`.

### 2. Overview (`overview.tex`)

- `thm:main-ergodic` → `CantorSzemeredi.main_ergodic`. Not started. Depends on the structure chapter.
- `cor:syndetic` → `CantorSzemeredi.syndetic_of_uniformLiminf_pos`. Done (`\leanok`).
- `thm:main-integers` → `CantorSzemeredi.main_integers`. Not started. Depends on the structure chapter.

## Next step

Start at `lem:chain-comparison` in `structure.tex`. Read the blueprint proof, write the Lean declaration in `Structure.lean`, build the module, check axioms, update the blueprint, and commit.
