import TauCeti.Analysis.Sobolev.W1p.Multiplication
import TauCeti.Analysis.Sobolev.W1p.Restriction

/-! EXPANSION.json precedes literal nested zero-boundary cutoff localization. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions Gradient
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E}

lemma restrict_contDiffSMul_ofTestFunction (hU : U ≤ Omega)
    (psi : E → ℝ) (hpsi : ContDiff ℝ ∞ psi) {M : ℝ} (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (phi : 𝓓(Omega, ℝ)) (Phi : 𝓓(U, ℝ))
    (hPhi : (Phi : E → ℝ) = psi * (phi : E → ℝ)) :
    TauCeti.W1p.restrictL hU (TauCeti.W1p.contDiffSMul psi hpsi hM hpsiM hgradM
        (TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi)) =
      TauCeti.W1p.ofTestFunctionₗ mu U 2 Phi := by
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  have hMu : mu.restrict U ≤ mu.restrict Omega :=
    Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)
  have hMul := (TauCeti.W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM
    (TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi)).filter_mono (ae_mono hMu)
  have hTest := (TauCeti.testFunctionLp_apply_ae (mu := mu) 2 phi).filter_mono (ae_mono hMu)
  filter_upwards [TauCeti.W1p.value_restrictL_ae hU
      (TauCeti.W1p.contDiffSMul psi hpsi hM hpsiM hgradM
        (TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi)), hMul,hTest,
    TauCeti.testFunctionLp_apply_ae (mu := mu) 2 Phi] with x hRestr hProduct hphi hPhiX
  rw [hRestr,hProduct,TauCeti.W1p.value_ofTestFunctionₗ,hphi,
    TauCeti.W1p.value_ofTestFunctionₗ,hPhiX,hPhi,Pi.mul_apply,smul_eq_mul]

lemma restrict_contDiffSMul_mem_w1p0Submodule (hU : U ≤ Omega)
    (psi : E → ℝ) (hpsi : ContDiff ℝ ∞ psi) {M : ℝ} (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (hSupport : tsupport psi ∩ (Omega : Set E) ⊆ (U : Set E))
    {u : TauCeti.W1p mu Omega 2} (hu : u ∈ TauCeti.w1p0Submodule mu Omega 2) :
    TauCeti.W1p.restrictL hU (TauCeti.W1p.contDiffSMul psi hpsi hM hpsiM hgradM u) ∈
      TauCeti.w1p0Submodule mu U 2 := by
  let L : TauCeti.W1p mu Omega 2 →L[ℝ] TauCeti.W1p mu U 2 :=
    (TauCeti.W1p.restrictL hU).comp (TauCeti.W1p.contDiffSMulL psi hpsi hM hpsiM hgradM)
  have hClosed : IsClosed (L ⁻¹' (TauCeti.w1p0Submodule mu U 2 : Set (TauCeti.W1p mu U 2))) :=
    (TauCeti.w1p0Submodule mu U 2).isClosed.preimage L.continuous
  have hTests : ∀ phi : 𝓓(Omega, ℝ), TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi ∈
      L ⁻¹' (TauCeti.w1p0Submodule mu U 2 : Set (TauCeti.W1p mu U 2)) := by
    intro phi
    have hSub : tsupport (psi * (phi : E → ℝ)) ⊆ (U : Set E) := by
      intro x hx
      exact hSupport ⟨tsupport_mul_subset_left hx,phi.tsupport_subset (tsupport_mul_subset_right hx)⟩
    let Phi : 𝓓(U, ℝ) := ⟨psi * (phi : E → ℝ),hpsi.mul phi.contDiff,
      phi.hasCompactSupport.mul_left,hSub⟩
    have hEq := restrict_contDiffSMul_ofTestFunction (mu := mu) hU psi hpsi hM hpsiM hgradM phi Phi rfl
    simpa only [L,Set.mem_preimage,SetLike.mem_coe,ContinuousLinearMap.comp_apply,
      TauCeti.W1p.contDiffSMulL_apply,hEq] using
      (TauCeti.W1p.ofTestFunctionₗ_mem_w1p0Submodule (mu := mu) (p := 2) Phi)
  have hMember := TauCeti.w1p0Submodule_subset_of_isClosed hClosed hTests hu
  simpa only [L,Set.mem_preimage,SetLike.mem_coe,ContinuousLinearMap.comp_apply,
    TauCeti.W1p.contDiffSMulL_apply] using hMember

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.restrict_contDiffSMul_ofTestFunction
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.restrict_contDiffSMul_mem_w1p0Submodule
