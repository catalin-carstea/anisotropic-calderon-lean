import Calderon.MixedKernelConstruction.MixedKernelMonotoneCurrentPair
import Calderon.MixedKernelConstruction.MixedKernelPositiveChartAgreement
import Calderon.MixedKernelConstruction.MixedKernelObservedOutputRooms
import Calderon.MixedKernelConstruction.MixedKernelCurrentCommonPair
import Calderon.MixedKernelConstruction.MixedKernelProductOpenUCP
import Calderon.MixedKernelConstruction.MixedKernelCenteredRooms
import Calderon.MixedKernelConstruction.MixedKernelFiniteInterpolation
import Calderon.MixedKernelConstruction.MixedKernelKnownSideNearOne
import Calderon.MixedKernelConstruction.MixedKernelAnnulusGeometry
import Calderon.MixedKernelConstruction.MixedKernelKnownSideCompactBuffer
import Calderon.MixedKernelConstruction.MixedKernelActualSeparatorAnchors
import Calderon.MixedKernelConstruction.MixedKernelKnownSideNeighborhood
import Calderon.MixedKernelConstruction.MixedKernelCompatibleGluing
import Calderon.MixedKernelConstruction.MixedKernelFullCrossAssembly
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

open Geometry





section RestrictedFactorJets
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

/-- SL-0: an `L²(O)` class a.e. equal to a smooth literal solution on open `O` is a class of the
harmonic space on `O` (it lies in the generating set of the closure). -/
theorem smoothClass_mem_harmonicSub (O : Set R3) (hO : IsOpen O)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A O) (b : R3 → ℝ)
    (hb : ContDiffOn ℝ ∞ b O) (hP : ∀ x ∈ O, divCoeffGrad A b x = 0)
    (g : Lp ℝ 2 ((volume : Measure R3).restrict O))
    (hg : (g : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict O] b) :
    g ∈ harmonicSub O hO A hA := by
  change g ∈ Regularity.classicalHarmonicL2Space O hO A hA
  unfold Regularity.classicalHarmonicL2Space
  exact Submodule.mem_closure_iff.mpr (Submodule.le_topologicalClosure _ ⟨b, hb, hP, hg⟩)

/-- SL-1: the restriction `R_O u` of an actual `D`-harmonic class to an open `O ⊆ D` is a class
of the harmonic space on `O` (the `D`-representative restricts; no extension is used). -/
theorem harmonicRestrict_mem_harmonicSub (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (hpos : ∀ x ∈ D, (A x).PosDef) (O : Set R3) (hO : IsOpen O) (hOD : O ⊆ D)
    (u : harmonicSub D hD A hA) :
    harmonicRestrict D hD A hA O hOD u ∈ harmonicSub O hO A (hA.mono hOD) := by
  obtain ⟨hU, hUae, hUP⟩ := harmonicRep_spec D hD A hA hpos u
  exact smoothClass_mem_harmonicSub O hO A (hA.mono hOD) _ (hU.mono hOD)
    (fun x hx => hUP x (hOD hx)) _ ((harmonicRestrict_ae D hD A hA O hOD u).trans
      (ae_restrict_of_ae_restrict_of_subset hOD hUae.symm))

/-- SL-2 (name): the smooth `O`-representative of the SAME restricted class `R_O u`. -/
def restrictRep (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (hpos : ∀ x ∈ D, (A x).PosDef) (O : Set R3) (hO : IsOpen O) (hOD : O ⊆ D)
    (u : harmonicSub D hD A hA) : R3 → ℝ :=
  harmonicRep O hO A (hA.mono hOD) (fun x hx => hpos x (hOD hx))
    ⟨harmonicRestrict D hD A hA O hOD u,
      harmonicRestrict_mem_harmonicSub D hD A hA hpos O hO hOD u⟩

/-- SL-3: the restricted representative is smooth on `O`, solves the literal equation there, is
a.e. the SAME class `R_O u`, and on every compact `K ⊆ O`, for every order `n`, all its
derivatives are bounded by `C ‖R_O u‖` with `C` chosen BEFORE `u` (C3Jets compact jet bound on
the room `O` itself, not on `D`). -/
theorem restrictRep_spec_and_jet_bound (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (hpos : ∀ x ∈ D, (A x).PosDef) (O : Set R3) (hO : IsOpen O) (hOD : O ⊆ D) :
    (∀ u : harmonicSub D hD A hA,
      ContDiffOn ℝ ∞ (restrictRep D hD A hA hpos O hO hOD u) O ∧
      restrictRep D hD A hA hpos O hO hOD u =ᵐ[(volume : Measure R3).restrict O]
        (harmonicRestrict D hD A hA O hOD u : R3 → ℝ) ∧
      ∀ x ∈ O, divCoeffGrad A (restrictRep D hD A hA hpos O hO hOD u) x = 0) ∧
    ∀ K : Set R3, IsCompact K → K ⊆ O → ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : harmonicSub D hD A hA, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ n (restrictRep D hD A hA hpos O hO hOD u) x‖ ≤
          C * ‖harmonicRestrict D hD A hA O hOD u‖ := by
  refine ⟨fun u => harmonicRep_spec O hO A (hA.mono hOD) (fun x hx => hpos x (hOD hx)) _, ?_⟩
  intro K hK hKO n
  obtain ⟨C, hC, hbound⟩ := harmonicRep_jet_bound_on_compact O hO A (hA.mono hOD)
    (fun x hx => hpos x (hOD hx)) K hK hKO n
  exact ⟨C, hC, fun u x hx => hbound _ x hx⟩

/-- SL-4: the ACTUAL first factor. For the SAME family `fᵢ = R_{O1} wᵢ` with the actual arm bound
`‖fᵢ‖ ≤ K₁ μᵢ^γ₁`, the smooth representatives `Wᵢ` have every order-`n` derivative on a compact
`K ⊆ O1` bounded by `C K₁ μᵢ^γ₁`, with `C` independent of the basis index. -/
theorem firstFactor_jet_bound (S : KnownSideSourceData) (lam : ℝ) (D1 : Set R3)
    (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (K : Set R3) (hK : IsCompact K) (hKO1 : K ⊆ O1) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type}
      (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ) (K1i γ1 : ℝ),
      (∀ i, ‖firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i‖ ≤ K1i * μ i ^ γ1) →
      ∀ i, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ n (restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i)) x‖ ≤
          C * (K1i * μ i ^ γ1) := by
  obtain ⟨C, hC, hbound⟩ := (restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1).2 K hK hKO1 n
  refine ⟨C, hC, fun w μ K1i γ1 hw i x hx => ?_⟩
  exact (hbound (w i) x hx).trans (mul_le_mul_of_nonneg_left (hw i) hC)

/-- SL-5a: a smooth solution `b` of the literal equation on open `O` with an `L²(O)` class `g`
has every order-`n` derivative on a compact `K ⊆ O` bounded by `C ‖g‖`, `C` chosen BEFORE `b`.
(`g` is a harmonic class on `O`; its C3Jets representative equals `b` on `O` by continuity.) -/
theorem smoothSolution_jet_bound (O : Set R3) (hO : IsOpen O)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A O)
    (hpos : ∀ x ∈ O, (A x).PosDef) (K : Set R3) (hK : IsCompact K) (hKO : K ⊆ O) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : R3 → ℝ, ContDiffOn ℝ ∞ b O → (∀ x ∈ O, divCoeffGrad A b x = 0) →
      ∀ g : Lp ℝ 2 ((volume : Measure R3).restrict O),
        b =ᵐ[(volume : Measure R3).restrict O] (g : R3 → ℝ) →
        ∀ x ∈ K, ‖iteratedFDeriv ℝ n b x‖ ≤ C * ‖g‖ := by
  obtain ⟨C, hC, hbound⟩ := harmonicRep_jet_bound_on_compact O hO A hA hpos K hK hKO n
  refine ⟨C, hC, fun b hb hP g hg x hx => ?_⟩
  have hmem : g ∈ harmonicSub O hO A hA :=
    smoothClass_mem_harmonicSub O hO A hA b hb hP g hg.symm
  let u : harmonicSub O hO A hA := ⟨g, hmem⟩
  obtain ⟨hU, hUae, -⟩ := harmonicRep_spec O hO A hA hpos u
  have hEq : EqOn (harmonicRep O hO A hA hpos u) b O :=
    Measure.eqOn_open_of_ae_eq (hUae.trans hg.symm) hO hU.continuousOn hb.continuousOn
  have hloc : harmonicRep O hO A hA hpos u =ᶠ[𝓝 x] b :=
    Filter.eventually_of_mem (hO.mem_nhds (hKO hx)) hEq
  rw [← (hloc.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
  exact hbound u x hx

end RestrictedFactorJets

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
