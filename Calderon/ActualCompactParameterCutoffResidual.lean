import Calderon.MixedKernelConstruction.MixedKernelClosedUniformFoundation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem exists_joint_compact_cutoff_residual_pointwise_bound
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a:E→Fin 3→Fin 3→R3→ℝ) (ha:∀ i j,JointSmooth fun P => a P i j)
    (hs:∀ P i j x,a P i j x=a P j i x) (A:Set E) (hA:IsCompact A)
    {chi beta:R3→ℝ} (hchi:ContDiff ℝ ∞ chi) (hbeta:Continuous beta)
    {K:Set R3} (hK:IsCompact K) :
    ∃ C:ℝ,0 ≤ C ∧ ∀ P∈A,∀ w:R3→ℝ,ContDiff ℝ ∞ w →
      (∀ x∈K,Lop (a P) w x=0) → ∀ x∈K,
      (beta x*Lop (a P) (fun y => chi y*w y) x)^2 ≤ C*(w x^2+∑ j,pd j w x^2) := by
  let c:E→R3→ℝ := fun P => Lop (a P) chi
  let q:E→Fin 3→R3→ℝ := fun P j x => 2*∑ i,a P i j x*pd i chi x
  have hchiJ : JointSmooth (fun _:E => chi) := hchi.comp contDiff_snd
  have hc : JointSmooth c := jointSmooth_Lop ha hchiJ
  have hq : ∀ j,JointSmooth (fun P => q P j) := by
    intro j
    exact jointSmooth_const_mul 2 (jointSmooth_sum
      (F:=fun i P x => a P i j x*pd i chi x)
      (fun i => jointSmooth_mul (ha i j) (jointSmooth_pd hchiJ i)))
  let F:E×R3→ℝ := fun z => beta z.2^2*(c z.1 z.2^2+∑ j,q z.1 j z.2^2)
  have hFc : Continuous F := ((hbeta.comp continuous_snd).pow 2).mul
    ((hc.continuous.pow 2).add (continuous_finsetSum _ fun j _ => (hq j).continuous.pow 2))
  obtain ⟨M0,hM0⟩ := (hA.prod hK).exists_bound_of_continuousOn hFc.continuousOn
  refine ⟨max M0 0,le_max_right _ _,?_⟩
  intro P hP w hw hLw x hx
  have hAbs : |F (P,x)| ≤ M0 := by
    simpa only [Real.norm_eq_abs] using hM0 (P,x) ⟨hP,hx⟩
  have hF : F (P,x) ≤ max M0 0 :=
    (le_abs_self _).trans (hAbs.trans (le_max_left _ _))
  have hcomm := CutoffCommutator.Lop_mul_symm (a P)
    (fun i j => jointSmooth_slice (ha i j) P) (hs P) hchi hw x
  rw [hLw x hx] at hcomm
  have heq : Lop (a P) (fun y => chi y*w y) x=c P x*w x+∑ j,q P j x*pd j w x := by
    rw [hcomm]
    simp only [c,q,Fin.sum_univ_three]
    ring
  rw [heq]
  have hCS := affine_three_sq_le (c P x) (w x) (fun j => q P j x) (fun j => pd j w x)
  calc
    _ = beta x^2*(c P x*w x+∑ j,q P j x*pd j w x)^2 := mul_pow _ _ 2
    _ ≤ beta x^2*((c P x^2+∑ j,q P j x^2)*(w x^2+∑ j,pd j w x^2)) :=
      mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = F (P,x)*(w x^2+∑ j,pd j w x^2) := by dsimp only [F];ring
    _ ≤ max M0 0*(w x^2+∑ j,pd j w x^2) := mul_le_mul_of_nonneg_right hF
      (add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))

theorem exists_joint_compact_cutoff_residual_pointwise_bound_local
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a:E→Fin 3→Fin 3→R3→ℝ) (ha:∀ i j,JointSmooth fun P => a P i j)
    (hs:∀ P i j x,a P i j x=a P j i x) (A:Set E) (hA:IsCompact A)
    {D K:Set R3} (hD:IsOpen D) (hK:IsCompact K) (hKD:K⊆D)
    {chi beta:R3→ℝ} (hchi:ContDiff ℝ ∞ chi) (hchic:HasCompactSupport chi)
    (htc:tsupport chi⊆D) (hbeta:Continuous beta) :
    ∃ C:ℝ,0 ≤ C ∧ ∀ P∈A,∀ w:R3→ℝ,ContDiffOn ℝ ∞ w D →
      (∀ x∈D,Lop (a P) w x=0) → ∀ x∈K,
      (beta x*Lop (a P) (fun y => chi y*w y) x)^2 ≤ C*(w x^2+∑ j,pd j w x^2) := by
  obtain ⟨zeta,hzeta,-,hzD,hz1⟩ := CutoffCommutator.exists_plateau_cutoff hD (hK.union hchic)
    (Set.union_subset hKD htc)
  obtain ⟨C,hC,hb⟩ := exists_joint_compact_cutoff_residual_pointwise_bound a ha hs A hA hchi hbeta hK
  refine ⟨C,hC,?_⟩
  intro P hP w hw hLw x hx
  have hW : ContDiff ℝ ∞ (fun y => zeta y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hD hzeta hzD hw
  have hgerm : ∀ y ∈ K, (fun y => zeta y * w y) =ᶠ[𝓝 y] w := fun y hy => by
    filter_upwards [hz1 y (Or.inl hy)] with z hz
    rw [hz, one_mul]
  have hchiW : (fun y => chi y * (zeta y * w y)) = fun y => chi y * w y := by
    funext y
    by_cases hy : y ∈ tsupport chi
    · rw [(hz1 y (Or.inr hy)).eq_of_nhds, one_mul]
    · have h0 : chi y = 0 := (notMem_tsupport_iff_eventuallyEq.mp hy).eq_of_nhds
      rw [h0, zero_mul, zero_mul]
  have hLW : ∀ y ∈ K, Lop (a P) (fun y => zeta y * w y) y = 0 := fun y hy => by
    rw [Lop_congr_of_eventuallyEq (a P) (hgerm y hy)]
    exact hLw y (hKD hy)
  have h := hb P hP _ hW hLW x hx
  rw [hchiW] at h
  have hval : zeta x * w x = w x := by rw [(hz1 x (Or.inl hx)).eq_of_nhds, one_mul]
  have hpdx : ∀ j, pd j (fun y => zeta y * w y) x = pd j w x := fun j =>
    pd_congr_of_eventuallyEq (hgerm x hx) j
  simp only [hval, hpdx] at h
  exact h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
