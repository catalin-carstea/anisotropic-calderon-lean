import Calderon.FramedEndpointLocalChart

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError

/-- A smooth chart for a map smooth on a genuine open domain. -/
theorem exists_smooth_local_chart_of_isOpen_of_isInvertible_fderiv
    (f : R3 → R3) (O : Set R3) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (z : R3) (hz : z ∈ O)
    (hD : (fderiv ℝ f z).IsInvertible) :
    ∃ e : OpenPartialHomeomorph R3 R3,
      (e : R3 → R3) = f ∧ z ∈ e.source ∧ f z ∈ e.target ∧
      e.source ⊆ O ∧ ContDiffOn ℝ ∞ f e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨D, hDeq⟩ := hD
  have hfz : ContDiffAt ℝ ∞ f z := hf.contDiffAt (hO.mem_nhds hz)
  have hfd : HasFDerivAt f (D : R3 →L[ℝ] R3) z := by
    rw [hDeq]
    exact (hfz.differentiableAt (by simp)).hasFDerivAt
  let e0 := hfz.toOpenPartialHomeomorph f hfd (by simp)
  let U : Set R3 := O ∩ (fderiv ℝ f) ⁻¹' {J | J.IsInvertible}
  have hU : IsOpen U :=
    (hf.continuousOn_fderiv_of_isOpen hO (by simp)).isOpen_inter_preimage hO
      ContinuousLinearMap.isOpen_setOfPred_isInvertible
  let e := e0.restrOpen U hU
  have hsource : e.source = e0.source ∩ U := e0.restrOpen_source U hU
  have hsub : e.source ⊆ O := fun x hx => ((hsource ▸ hx).2).1
  have heq : (e : R3 → R3) = f := rfl
  have hze : z ∈ e.source := by
    rw [hsource]
    exact ⟨hfz.mem_toOpenPartialHomeomorph_source hfd (by simp), hz, ⟨D, hDeq⟩⟩
  refine ⟨e, heq, hze, e.map_source hze, hsub, hf.mono hsub, ?_⟩
  intro q hq
  have hx : e.symm q ∈ e.source := e.map_target hq
  have hfx : ContDiffAt ℝ ∞ f (e.symm q) :=
    hf.contDiffAt (hO.mem_nhds (hsub hx))
  have hInv : (fderiv ℝ f (e.symm q)).IsInvertible := (hsource ▸ hx).2.2
  obtain ⟨Dq, hDq⟩ := hInv
  have hdq : HasFDerivAt e (Dq : R3 →L[ℝ] R3) (e.symm q) := by
    change HasFDerivAt f (Dq : R3 →L[ℝ] R3) (e.symm q)
    rw [hDq]
    exact (hfx.differentiableAt (by simp)).hasFDerivAt
  exact (e.contDiffAt_symm hq hdq hfx).contDiffWithinAt

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.exists_smooth_local_chart_of_isOpen_of_isInvertible_fderiv
