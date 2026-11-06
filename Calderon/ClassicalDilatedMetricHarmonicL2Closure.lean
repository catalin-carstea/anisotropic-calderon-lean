import Calderon.ClassicalHarmonicL2Space
import Calderon.ClassicalDilatedMetricHarmonicL2Jets
import Calderon.MetricSmooth
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSpace.Basic

noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal BigOperators Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity
open EnergyBridge

theorem classicalDilatedMetricHarmonicL2Submodule_closure_and_representatives
    (a : MatrixField) (ha : IsAdmissibleMetric a)
    (lambda : ℝ) (D : Set R3) (hD : IsOpen D) :
    let A : MatrixField := principalCoefficient (fun y : R3 => a (lambda • y))
    let hA : ContDiffOn ℝ ∞ A D :=
      ((contDiff_principalCoefficient a ha).comp (contDiff_const_smul lambda)).contDiffOn
    let S0 := classicalDilatedMetricHarmonicL2Submodule a ha lambda D hD
    let H := classicalHarmonicL2Space D hD A hA
    (∀ u : Lp ℝ 2 ((volume : Measure R3).restrict D),
      u ∈ S0 ↔ ∃ f : R3 → ℝ, ContDiffOn ℝ ∞ f D ∧
        (∀ x ∈ D, divCoeffGrad A f x = 0) ∧
        (u : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D] f) ∧
    S0.closure = H ∧
    (∃ e : S0 →ₗᵢ[ℝ] H, DenseRange e ∧
      ∀ v : S0,
        (e v : Lp ℝ 2 ((volume : Measure R3).restrict D)) =
          (v : Lp ℝ 2 ((volume : Measure R3).restrict D))) ∧
    (∀ w : H, ∃ f : R3 → ℝ, ContDiffOn ℝ ∞ f D ∧
      (∀ x ∈ D, divCoeffGrad A f x = 0) ∧
      ∃ hf : MemLp f 2 ((volume : Measure R3).restrict D),
        hf.toLp f = (w : Lp ℝ 2 ((volume : Measure R3).restrict D))) ∧
    (∀ (w : H) (f g : R3 → ℝ),
      ContDiffOn ℝ ∞ f D → (∀ x ∈ D, divCoeffGrad A f x = 0) →
      ∀ hf : MemLp f 2 ((volume : Measure R3).restrict D),
      hf.toLp f = (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) →
      ContDiffOn ℝ ∞ g D → (∀ x ∈ D, divCoeffGrad A g x = 0) →
      ∀ hg : MemLp g 2 ((volume : Measure R3).restrict D),
      hg.toLp g = (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) →
        EqOn f g D ∧ ∀ m : ℕ,
          EqOn (iteratedFDeriv ℝ m f) (iteratedFDeriv ℝ m g) D) ∧
    ∀ (S : Set R3) (hS : IsOpen S) (hSD : S ⊆ D),
      let R : H →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S) :=
        (Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤)
          (show (volume : Measure R3).restrict S ≤
            (1 : ℝ≥0∞) • (volume : Measure R3).restrict D from
            by simpa only [one_smul] using Measure.restrict_mono_set volume hSD)).comp
          H.toSubmodule.subtypeL
      ‖R‖ ≤ 1 ∧
      ∀ (w : H) (f : R3 → ℝ), ContDiffOn ℝ ∞ f D →
        (∀ x ∈ D, divCoeffGrad A f x = 0) →
        ∀ hf : MemLp f 2 ((volume : Measure R3).restrict D),
          hf.toLp f = (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) →
          (R w : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict S] f
 := by
  classical
  intro A hA S0 H
  -- C0.0: original coefficient sampled at arbitrary signed lambda.
  have hpos : ∀ x ∈ D, (A x).PosDef := by
    intro x _hx
    change (principalCoefficient a (lambda • x)).PosDef
    exact principalCoefficient_posDef a ha (lambda • x)
  -- C0.1: the exact raw classical carrier, with both directions of the AE dictionary.
  have hClassIff (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) (f : R3 → ℝ) :
      (∃ hf : MemLp f 2 ((volume : Measure R3).restrict D), hf.toLp f = u) ↔
        (u : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D] f := by
    constructor
    · rintro ⟨hf, he⟩
      exact he ▸ hf.coeFn_toLp
    · intro hu
      have hf : MemLp f 2 ((volume : Measure R3).restrict D) :=
        MemLp.ae_eq hu (Lp.memLp u)
      refine ⟨hf, Lp.ext (hf.coeFn_toLp.trans hu.symm)⟩
  have hCarrier (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) :
      u ∈ S0 ↔ ∃ f : R3 → ℝ, ContDiffOn ℝ ∞ f D ∧
        (∀ x ∈ D, divCoeffGrad A f x = 0) ∧
        (u : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D] f := by
    change (∃ f : R3 → ℝ, ContDiffOn ℝ ∞ f D ∧
      (∀ x ∈ D, divCoeffGrad A f x = 0) ∧
      ∃ hf : MemLp f 2 ((volume : Measure R3).restrict D), hf.toLp f = u) ↔ _
    constructor
    · rintro ⟨f, hf, hp, hc⟩
      exact ⟨f, hf, hp, (hClassIff u f).mp hc⟩
    · rintro ⟨f, hf, hp, hc⟩
      exact ⟨f, hf, hp, (hClassIff u f).mpr hc⟩
  -- C0.2: actual genuine446 closure, no alternate space or completion.
  have hCarrierSet : (S0 : Set (Lp ℝ 2 ((volume : Measure R3).restrict D))) =
      {v : Lp ℝ 2 ((volume : Measure R3).restrict D) | ∃ f : R3 → ℝ,
        ContDiffOn ℝ ∞ f D ∧ (∀ x ∈ D, divCoeffGrad A f x = 0) ∧
          (v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D] f} :=
    Set.ext hCarrier
  have hClosure : S0.closure = H := by
    ext u
    change u ∈ closure (S0 : Set (Lp ℝ 2 ((volume : Measure R3).restrict D))) ↔
      u ∈ closure {v : Lp ℝ 2 ((volume : Measure R3).restrict D) | ∃ f : R3 → ℝ,
        ContDiffOn ℝ ∞ f D ∧ (∀ x ∈ D, divCoeffGrad A f x = 0) ∧
          (v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D] f}
    rw [hCarrierSet]
  -- C0.3: same-class inclusion into the actual closure is a dense isometry.
  have hSH : (S0 : Set (Lp ℝ 2 ((volume : Measure R3).restrict D))) ⊆
      (H : Set (Lp ℝ 2 ((volume : Measure R3).restrict D))) := by
    intro u hu
    rw [← hClosure]
    exact S0.le_topologicalClosure hu
  let e : S0 →ₗᵢ[ℝ] H :=
    { toFun := fun v => ⟨(v : Lp ℝ 2 ((volume : Measure R3).restrict D)), hSH v.property⟩
      map_add' := by intro v w; rfl
      map_smul' := by intro r v; rfl
      norm_map' := by intro v; rfl }
  have hDense : DenseRange e := by
    change DenseRange (Set.inclusion hSH)
    apply (denseRange_inclusion_iff hSH).mpr
    rw [← hClosure]
    exact Set.Subset.rfl
  refine ⟨hCarrier, hClosure, ⟨e, hDense, fun _ => rfl⟩, ?_, ?_, ?_⟩
  -- C0.4: the already checked global-on-D representative theorem applies to every w.
  · intro w
    have hw : (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) ∈
        closure {v : Lp ℝ 2 ((volume : Measure R3).restrict D) | ∃ f : R3 → ℝ,
          ContDiffOn ℝ ∞ f D ∧ (∀ x ∈ D, divCoeffGrad A f x = 0) ∧
            (v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D] f} := w.property
    obtain ⟨f, hf, hAE, hPDE⟩ :=
      exists_contDiffOn_representative_of_mem_closure_L2_classical_harmonics
        D hD A hA hpos (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) hw
    exact ⟨f, hf, hPDE, (hClassIff _ f).mpr hAE.symm⟩
  -- C0.5: equal classes give equal values and all ordinary jets on the same open D.
  · intro w f g hf _hfPDE hfMem hfClass hg _hgPDE hgMem hgClass
    have hfAE : ((w : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict D] f :=
      (hClassIff _ f).mp ⟨hfMem, hfClass⟩
    have hgAE : ((w : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict D] g :=
      (hClassIff _ g).mp ⟨hgMem, hgClass⟩
    have hEq : EqOn f g D :=
      Measure.eqOn_open_of_ae_eq (hfAE.symm.trans hgAE) hD hf.continuousOn hg.continuousOn
    refine ⟨hEq, ?_⟩
    intro m x hx
    have hGerm : f =ᶠ[𝓝 x] g :=
      Filter.eventually_of_mem (hD.mem_nhds hx) (fun _ hy => hEq hy)
    exact (hGerm.iteratedFDeriv ℝ m).eq_of_nhds
  -- C0.6: literal c=1 measure restriction, including trivial H and empty sets.
  · intro S hS hSD R
    have hRestr : (volume : Measure R3).restrict S ≤
        (1 : ℝ≥0∞) • (volume : Measure R3).restrict D := by
      simpa only [one_smul] using Measure.restrict_mono_set volume hSD
    let Q : Lp ℝ 2 ((volume : Measure R3).restrict D) →L[ℝ]
        Lp ℝ 2 ((volume : Measure R3).restrict S) :=
      Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤) hRestr
    have hQ : ‖Q‖ ≤ 1 := by
      simpa only [ENNReal.toReal_one, Real.one_rpow] using
        (Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := (2 : ℝ≥0∞))
          (by simp : (1 : ℝ≥0∞) ≠ ⊤) hRestr)
    refine ⟨R.opNorm_le_bound zero_le_one ?_, ?_⟩
    · intro w
      change ‖Q (w : Lp ℝ 2 ((volume : Measure R3).restrict D))‖ ≤ 1 * ‖w‖
      calc
        ‖Q (w : Lp ℝ 2 ((volume : Measure R3).restrict D))‖ ≤
            ‖Q‖ * ‖(w : Lp ℝ 2 ((volume : Measure R3).restrict D))‖ := Q.le_opNorm _
        _ ≤ 1 * ‖(w : Lp ℝ 2 ((volume : Measure R3).restrict D))‖ :=
          mul_le_mul_of_nonneg_right hQ (norm_nonneg _)
        _ = 1 * ‖w‖ := rfl
    · intro w f _hf _hfPDE hfMem hfClass
      have hR : (R w : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict S]
          ((w : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ) :=
        Lp.coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤) hRestr
          (w : Lp ℝ 2 ((volume : Measure R3).restrict D))
      have hAE : ((w : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ)
          =ᵐ[(volume : Measure R3).restrict D] f :=
        (hClassIff _ f).mp ⟨hfMem, hfClass⟩
      exact hR.trans (ae_restrict_of_ae_restrict_of_subset hSD hAE)

end OAI.AnisotropicCalderon.Regularity

#print axioms OAI.AnisotropicCalderon.Regularity.classicalDilatedMetricHarmonicL2Submodule_closure_and_representatives
