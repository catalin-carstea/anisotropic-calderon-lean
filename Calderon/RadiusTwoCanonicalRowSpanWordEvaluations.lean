import Calderon.RadiusTwoFinsuppLocalizedWordBounds
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Group.Submodule

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets

theorem exists_radiusTwo_canonical_rowSpan_word_evaluations
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (η : ℕ → 𝓓(radiusTwoOpens, ℝ)) (S : Set R3) (hS : MeasurableSet S)
    (hSupp : ∀ j : ℕ, tsupport (η j : R3 → ℝ) ⊆ S)
    (hOne : ∀ j : ℕ, ∀ z ∈ tsupport (η j : R3 → ℝ), η (j+1) z = 1)
    (P : Set R3) (hPB : P ⊆ (radiusTwoOpens : Set R3) \ S)
    (a₀ : ℝ) (ha₀ : 0 < a₀) (ha₀1 : a₀ < 1)
    (Z : Set R3) (hZ : IsOpen Z) (hZBall : Z ⊆ ball (0 : R3) (2*a₀))
    (hEtaOne : ∀ z ∈ Z, η 0 z = 1) :
    let ν : Measure R3 := ((volume : Measure R3).restrict radiusTwoOpens).restrict S
    let R : RadiusTwoL2 →L[ℝ] Lp ℝ 2 ν := MeasureTheory.LpToLpRestrictCLM R3 ℝ ℝ
      ((volume : Measure R3).restrict radiusTwoOpens) 2 S
    let F : P → Lp ℝ 2 ν := fun p => R (K ⟨p,(hPB p.property).1⟩)
    let Y : Submodule ℝ (Lp ℝ 2 ν) :=
      (Submodule.span ℝ (Set.range F)).topologicalClosure
    let liftRows : P → Y := fun p => ⟨F p,
      (Submodule.le_topologicalClosure _)
        (Submodule.subset_span (show F p ∈ Set.range F from ⟨p,rfl⟩))⟩
    let e : (P →₀ ℝ) →ₗ[ℝ] Y := Finsupp.linearCombination ℝ liftRows
    ∃ C : ℕ → ℝ, (∀ n : ℕ, 0 ≤ C n) ∧
      ∃ L : List (Fin 3) → R3 → Y →L[ℝ] ℝ,
        ∀ (w : List (Fin 3)) (z : R3), z ∈ Z →
          ‖L w z‖ ≤ C w.length ∧
          (∀ c : P →₀ ℝ, L w z (e c) = Finsupp.linearCombination ℝ
            (fun p : P => coordinateFieldWordPartial w (G ⟨p,(hPB p.property).1⟩) z) c) ∧
          (∀ p : P, L w z (liftRows p) =
            coordinateFieldWordPartial w (G ⟨p,(hPB p.property).1⟩) z) ∧
          ∀ T : Y →L[ℝ] ℝ,
            (∀ c : P →₀ ℝ, T (e c) = Finsupp.linearCombination ℝ
              (fun p : P => coordinateFieldWordPartial w (G ⟨p,(hPB p.property).1⟩) z) c) →
            T = L w z := by
  classical
  intro ν R F Y liftRows e
  have hActual := exists_radiusTwo_finsupp_localized_word_bound
    hreg hcalc g hg K G hData η S hS hSupp hOne P hPB
    a₀ ha₀ ha₀1 Z hZ hZBall hEtaOne
  rcases hActual with ⟨C,hC,hActual⟩
  have hDense : DenseRange e := by
    simpa only [F] using denseRange_radiusTwo_restrictedRow_linearCombination
      K S P (fun p hp => (hPB hp).1)
  let f : List (Fin 3) → R3 → (P →₀ ℝ) →ₗ[ℝ] ℝ := fun w z =>
    Finsupp.linearCombination ℝ
      (fun p : P => coordinateFieldWordPartial w (G ⟨p,(hPB p.property).1⟩) z)
  have hValue (c : P →₀ ℝ) : Y.subtypeL (e c) =
      Finsupp.linearCombination ℝ F c := by
    simp only [e, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_smul, Submodule.subtypeL_apply, liftRows]
  have hNorme (c : P →₀ ℝ) : ‖e c‖ = ‖Finsupp.linearCombination ℝ F c‖ := by
    calc
      ‖e c‖ = ‖Y.subtypeL (e c)‖ := (Submodule.norm_coe (e c)).symm
      _ = ‖Finsupp.linearCombination ℝ F c‖ := congrArg norm (hValue c)
  have hBound (w : List (Fin 3)) (z : R3) (hz : z ∈ Z) (c : P →₀ ℝ) :
      ‖f w z c‖ ≤ C w.length * ‖e c‖ := by
    rw [hNorme c]
    simpa only [f, Real.norm_eq_abs] using hActual c w z hz
  let L : List (Fin 3) → R3 → Y →L[ℝ] ℝ := fun w z => (f w z).extendOfNorm e
  refine ⟨C,hC,L,?_⟩
  intro w z hz
  have hAction (c : P →₀ ℝ) : L w z (e c) = f w z c := by
    exact LinearMap.extendOfNorm_eq hDense ⟨C w.length,hBound w z hz⟩ c
  refine ⟨?_,hAction,?_,?_⟩
  · exact LinearMap.opNorm_extendOfNorm_le hDense (hC w.length) (hBound w z hz)
  · intro p
    have h := hAction (Finsupp.single p (1 : ℝ))
    simpa only [e, f, Finsupp.linearCombination_single, one_smul] using h
  · intro T hT
    have hFormal : T.toLinearMap.comp e = f w z := by
      apply LinearMap.ext
      intro c
      exact hT c
    exact (LinearMap.extendOfNorm_unique hDense (C w.length)
      (hBound w z hz) T hFormal).symm

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_canonical_rowSpan_word_evaluations
