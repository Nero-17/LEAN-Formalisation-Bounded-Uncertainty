# Third-party proof provenance

These files preserve the licenses and immutable source references for the external proof foundations used during the Section 4 formalization. The project continues to use Lean 4.28.0 and its existing pinned mathlib; no dependency revision was changed.

## Cubical Sperner and Brouwer: harfe, MIT

Source repository: [harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838). The imported version is commit `770940ddf9878cf61952ed53d910b92bca841838`, whose `LICENSE` grants the MIT license and whose actual `lean-toolchain` specifies Lean 4.32.0. Copyright and the complete license are retained in [Harfe-MIT.txt](Harfe-MIT.txt).

| Original path below `FixedPointTheorems/` | Project module below `BoundedUncertainty/` | SHA-256 of original downloaded bytes |
| --- | --- | --- |
| `cubical_sperner_prep.lean` | `VendorSpernerPrep.lean` | `DBC747F080B54B79FFC77F1ADACEC7C964DAF56DC5210C0DDFF1350B42343F43` |
| `cubical_sperner.lean` | `VendorSperner.lean` | `EDD0295E8F0AE1E572D82705E89594F7069796877572563C9750A3D82AB0B005` |
| `apply_cubical_sperner.lean` | `VendorSpernerApplication.lean` | `D059B34AA7AD20CD07020EED07FA7A217F67FE7C2C6324E94345AB85D68B50EE` |
| `convex_homeos.lean` | `VendorConvexHomeomorphisms.lean` | `C9EE9D5B6CE22A8D84D1B391F7A77DE2E12A5A13C5CB12F723B61E287436269A` |
| `brouwer.lean` | `VendorBrouwer.lean` | `B014D761A559ABBB87EEBE4299191571C85DE37F2D967EF0EE16E1EC2148D7DE` |

All five files received attribution headers, project-relative imports, and the enclosing namespace `BoundedUncertainty.Vendor`. Mathematical helper names and definitions were preserved. The only proof compatibility change is in the final induction step of `strong_cubical_sperner`: the original

```lean
exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
  ⟨Finset.mem_univ I, (hcomp I).mp (h4 ▸ h3)⟩)
```

became

```lean
exact (hcomp I).mp (h4 ▸ h3)
```

Lean 4.28 has already simplified the goal from finite-set membership to its defining predicate at that point. The enclosed proof proves that predicate directly. No mathematical assumption or conclusion changed.

The earlier Lean 4.27 commit `7c9944876b54a7d5fcdbd542f56385b33c0d2e90` was downloaded and compiled only as a compatibility probe. It predates the repository's license file and is **not** the source version copied into these modules. The current MIT-licensed version proved compatible with the single change above.

The formal foundation proves a fixed point for every continuous self-map of every nonempty compact convex subset of a finite-dimensional real normed space. Its actual dependency chain is cubical grid geometry, counting/parity, arbitrarily close labeled points, compact subsequence extraction, and a homeomorphism from an arbitrary compact convex set to a cube in its affine dimension. The final statement contains no no-retraction or fixed-point assumption.

## Invariance of domain: Kai Lam, Apache 2.0

Source: [mathlib pull request 36770](https://github.com/leanprover-community/mathlib4/pull/36770), immutable branch commit `230d75acb32d80e7d7c4f4cd028b139f3dc28be7` in `Xmask19/mathlib4`. Original path: `Mathlib/AlgebraicTopology/InvarianceOfDomain.lean`. The original file attributes Kai Lam and uses Apache 2.0. The complete license from that exact commit is retained in [KaiLam-Apache-2.0.txt](KaiLam-Apache-2.0.txt).

SHA-256 of the full original source: `E0E6DC4EB41A3F02AC9A702ED9BA15D4A8EBB779F07524EEF055CAF875329D7D`.

`InvarianceOfDomainFromBrouwer.lean` extracts the differentiable approximation lemma (original lines 1014–1113) and the subsequent stability-of-zero, unit-ball interior, and open-image proof through original line 1438. The upstream file also contains unfinished, earlier proof experiments. Those experiments are not imported or copied as dependencies. The extracted proof takes an explicit `BrouwerFixedPoint` structure argument, replacing the upstream assumed typeclass interface; `BoundedUncertainty.brouwerFixedPoint_proved` in the project supplies this certificate from the proved MIT-licensed foundation above. The port handles the zero-dimensional case explicitly by proving the image is the entire subsingleton space before entering the nontrivial-space approximation argument. See that module's source for the exact extracted interfaces and compatibility changes.

The mathematical exposition used by the upstream proof is [Terence Tao, “Brouwer's fixed point and invariance of domain theorems, and Hilbert's fifth problem” (2011)](https://terrytao.wordpress.com/2011/06/13/brouwers-fixed-point-and-invariance-of-domain-theorems-and-hilberts-fifth-problem/). The upstream proof and the local adaptation retain their original authorship; local integration and verification do not claim authorship of the underlying arguments.
