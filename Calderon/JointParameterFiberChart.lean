import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Tactic

/-! Source-only generic joint chart construction. Full expansion C1--C3 and
exact typed interfaces were sealed before authoring. ROOT owns checking. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def parameterFiberDerivative (f : P × V → V) (a : P × V) : V →L[ℝ] V :=
  (fderiv ℝ f a).comp (ContinuousLinearMap.inr ℝ P V)

def parameterFiberMap (f : P × V → V) (a : P × V) : P × V := (a.1,f a)

theorem contDiff_parameterFiberDerivative (f : P × V → V) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (parameterFiberDerivative f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

theorem hasFDerivAt_parameter_fiber_slice (f : P × V → V)
    (hf : ContDiff ℝ ∞ f) (p : P) (z : V) :
    HasFDerivAt (fun w => f (p,w)) (parameterFiberDerivative f (p,z)) z :=
  (hf.differentiable (by simp) (p,z)).hasFDerivAt.comp z
    (hasFDerivAt_prodMk_right p z)

theorem contDiff_parameterFiberMap (f : P × V → V) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (parameterFiberMap f) := contDiff_fst.prodMk hf

theorem isInvertible_fderiv_parameterFiberMap (f : P × V → V)
    (hf : ContDiff ℝ ∞ f) (a : P × V) (hD : (parameterFiberDerivative f a).IsInvertible) :
    (fderiv ℝ (parameterFiberMap f) a).IsInvertible := by
  let D : P × V →L[ℝ] V := fderiv ℝ f a
  let A : P →L[ℝ] V := D.comp (ContinuousLinearMap.inl ℝ P V)
  let L : P × V →L[ℝ] P × V := (ContinuousLinearMap.fst ℝ P V).prod D
  have hd : HasFDerivAt (parameterFiberMap f) L a :=
    hasFDerivAt_fst.prodMk (hf.differentiable (by simp) a).hasFDerivAt
  obtain ⟨eB,hBeq⟩ := hD
  let e : (P × V) ≃L[ℝ] (P × V) := (ContinuousLinearEquiv.refl ℝ P).skewProd eB A
  have heq : (e : P × V →L[ℝ] P × V) = L := by
    apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext
    · rfl
    · change (eB : V →L[ℝ] V) v.2 + A v.1 = D v
      rw [hBeq,add_comm]
      exact D.comp_inl_add_comp_inr v
  rw [hd.fderiv]
  exact ⟨e,heq⟩

variable [CompleteSpace P] [CompleteSpace V]

theorem exists_joint_open_chart_parameter_family (f : P × V → V)
    (hf : ContDiff ℝ ∞ f) (U : Set P) (Z : Set V) (hU : IsOpen U) (hZ : IsOpen Z)
    (hi : ∀ p ∈ U, InjOn (fun z => f (p,z)) Z)
    (hD : ∀ a ∈ U ×ˢ Z, (parameterFiberDerivative f a).IsInvertible) :
    ∃ e : OpenPartialHomeomorph (P × V) (P × V),
      (e : P × V → P × V) = parameterFiberMap f ∧
      e.source = U ×ˢ Z ∧ e.target = parameterFiberMap f '' (U ×ˢ Z) ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ a ∈ U ×ˢ Z, e.symm (parameterFiberMap f a) = a) ∧
      (∀ b ∈ e.target, parameterFiberMap f (e.symm b) = b) ∧
      ∀ b ∈ e.target, (e.symm b).1 = b.1 := by
  let S := parameterFiberMap f
  let W : Set (P × V) := U ×ˢ Z
  have hW : IsOpen W := hU.prod hZ
  have hS : ContDiff ℝ ∞ S := contDiff_parameterFiberMap f hf
  have hInj : InjOn S W := by
    intro a ha b hb hab
    have hp : a.1 = b.1 := by
      simpa only [S,parameterFiberMap] using congrArg (fun x : P × V => x.1) hab
    have hv : f (a.1,a.2) = f (b.1,b.2) := by
      simpa only [S,parameterFiberMap] using congrArg (fun x : P × V => x.2) hab
    apply Prod.ext hp
    rw [← hp] at hv
    exact (hi a.1 ha.1) ha.2 hb.2 hv
  have hFull (a : P × V) (ha : a ∈ W) : (fderiv ℝ S a).IsInvertible :=
    isInvertible_fderiv_parameterFiberMap f hf a (hD a ha)
  have ho : IsOpenMap (W.domRestrict S) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    obtain ⟨D,hDeq⟩ := hFull x x.property
    have hfd : HasFDerivAt S (D : P × V →L[ℝ] P × V) (x : P × V) := by
      rw [hDeq]
      exact (hS.differentiable (by simp) (x : P × V)).hasFDerivAt
    have hmap : Filter.map S (𝓝 (x : P × V)) = 𝓝 (S (x : P × V)) :=
      (hS.contDiffAt.hasStrictFDerivAt' hfd (by simp)).map_nhds_eq_of_equiv
    have hsub : Filter.map ((↑) : W → P × V) (𝓝 x) = 𝓝 (x : P × V) :=
      map_nhds_subtype_coe_eq_nhds x.property (hW.mem_nhds x.property)
    change 𝓝 (S (x : P × V)) ≤ Filter.map (S ∘ ((↑) : W → P × V)) (𝓝 x)
    rw [← Filter.map_map,hsub,hmap]
  let pe : PartialEquiv (P × V) (P × V) := hInj.toPartialEquiv S W
  let e : OpenPartialHomeomorph (P × V) (P × V) :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict pe hS.continuous.continuousOn ho hW
  have heq : (e : P × V → P × V) = S := rfl
  have hs : e.source = W := rfl
  have ht : e.target = S '' W := rfl
  refine ⟨e,heq,hs,ht,?_,?_,?_,?_⟩
  · intro b hb
    have ha : e.symm b ∈ W := by simpa only [hs] using e.map_target hb
    obtain ⟨D,hDeq⟩ := hFull (e.symm b) ha
    have hfd : HasFDerivAt e (D : P × V →L[ℝ] P × V) (e.symm b) := by
      change HasFDerivAt S (D : P × V →L[ℝ] P × V) (e.symm b)
      rw [hDeq]
      exact (hS.differentiable (by simp) (e.symm b)).hasFDerivAt
    exact (e.contDiffAt_symm hb hfd hS.contDiffAt).contDiffWithinAt
  · intro a ha
    have hasource : a ∈ e.source := by simpa only [hs] using ha
    exact e.left_inv hasource
  · intro b hb
    exact e.right_inv hb
  · intro b hb
    have hinv : S (e.symm b) = b := e.right_inv hb
    simpa only [S,parameterFiberMap] using congrArg (fun x : P × V => x.1) hinv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Full ambient inverse derivatives on a fixed compact subset of one open smooth domain. -/
theorem exists_compact_uniform_iteratedFDeriv_bound_on_open (G : E → F)
    (O : Set E) (hO : IsOpen O) (hG : ContDiffOn ℝ ∞ G O)
    (T : Set E) (hT : IsCompact T) (hTO : T ⊆ O) :
    ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N → ∀ x ∈ T,
      ‖iteratedFDeriv ℝ j G x‖ ≤ D := by
  have hsingle (j : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ T,
      ‖iteratedFDeriv ℝ j G x‖ ≤ D := by
    have hc : ContinuousOn (iteratedFDeriv ℝ j G) O :=
      ContinuousOn.continuousOn_iteratedFDeriv hG hO (by simp)
    obtain ⟨D,hD⟩ := hT.exists_bound_of_continuousOn (hc.mono hTO)
    exact ⟨max D 0,le_max_right _ _,fun x hx => (hD x hx).trans (le_max_left _ _)⟩
  choose D hD hb using hsingle
  intro N
  refine ⟨∑ j ∈ Finset.range (N+1),D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro j hj x hx
  have hmem : j ∈ Finset.range (N+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  exact (hb j x hx).trans (Finset.single_le_sum (fun k _ => hD k) hmem)

end OAI.AnisotropicCalderon.ConnectionError
