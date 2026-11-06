import MixedKernelObservedOutputRooms
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Filter Metric
open scoped Topology

/-- Scalar parameters for an asymmetric first-variable chamber, with exponent arbitrarily
close to one. The actual asymmetric cutoff/Carleman arm is a separate obligation. -/
theorem exists_asymmetric_height_exponent_close_one {k l beta : ℝ}
    (hk : 0 < k) (hl : 0 < l) (hkl : k*l < 1/8)
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) :
    ∃ h eps : ℝ, 0 < eps ∧ 4*eps < h ∧ h ≤ l ∧
      4*eps < k*l^2 ∧ k*(l+4*eps) < 1/4 ∧
      1-beta < (strictHeight k (-eps)-strictHeight k (-l+3*eps)) /
        (strictHeight k (h+3*eps)-strictHeight k (-l+3*eps)) ∧
      (strictHeight k (-eps)-strictHeight k (-l+3*eps)) /
        (strictHeight k (h+3*eps)-strictHeight k (-l+3*eps)) < 1 := by
  let gamma : ℝ → ℝ := fun h =>
    (strictHeight k (-(h/16))-strictHeight k (-l+3*(h/16))) /
      (strictHeight k (h+3*(h/16))-strictHeight k (-l+3*(h/16)))
  have hbase : 0 < strictHeight k 0-strictHeight k (-l) := by
    dsimp [strictHeight]
    nlinarith [mul_nonneg hk.le (sq_nonneg l)]
  have hcN : Continuous (fun h : ℝ => strictHeight k (-(h/16))-
      strictHeight k (-l+3*(h/16))) := by unfold strictHeight; fun_prop
  have hcD : Continuous (fun h : ℝ => strictHeight k (h+3*(h/16))-
      strictHeight k (-l+3*(h/16))) := by unfold strictHeight; fun_prop
  have hden0 : strictHeight k ((0:ℝ)+3*(0/16))-strictHeight k (-l+3*(0/16)) ≠ 0 := by
    simpa only [zero_div,mul_zero,zero_add,add_zero] using hbase.ne'
  have hc : ContinuousAt gamma 0 := hcN.continuousAt.div hcD.continuousAt hden0
  have hgamma0 : gamma 0 = 1 := by
    dsimp [gamma]
    simp only [zero_div,mul_zero,neg_zero,zero_add,add_zero]
    exact div_self hbase.ne'
  have hneigh : {h | 1-beta < gamma h} ∈ 𝓝 (0:ℝ) :=
    hc.preimage_mem_nhds (Ioi_mem_nhds (by rw [hgamma0]; linarith))
  obtain ⟨r,hr,hsmall⟩ := Metric.mem_nhds_iff.mp hneigh
  let h := min (r/2) (min (l/2) (min (1/(32*k)) (k*l^2/64)))
  have hh : 0 < h := by dsimp [h]; positivity
  have hhr : h ≤ r/2 := min_le_left _ _
  have hhl : h ≤ l/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hhk : h ≤ 1/(32*k) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhk2 : h ≤ k*l^2/64 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hkh : k*h ≤ 1/32 := by
    have hb := (le_div_iff₀ (by positivity : (0:ℝ) < 32*k)).mp hhk
    nlinarith
  let eps := h/16
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hgap : 4*eps < h := by dsimp [eps]; linarith
  have hepsl : 4*eps ≤ l/8 := by dsimp [eps]; linarith
  have hepsk : 4*eps < k*l^2 := by
    have hpos : 0 < k*l^2 := mul_pos hk (sq_pos_of_pos hl)
    dsimp [eps]
    linarith
  have hmargin : k*(l+4*eps) < 1/4 := by
    have hm := mul_le_mul_of_nonneg_left hepsl hk.le
    nlinarith
  have hnear : 1-beta < gamma h := by
    apply hsmall
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hh]
    linarith
  have hs : 0 < h+3*eps := by positivity
  have hks : k*(h+3*eps) ≤ 1/4 := by dsimp [eps]; nlinarith
  have hhigh : 0 < strictHeight k (h+3*eps) := by
    have hm := mul_pos hs (show 0 < 1-k*(h+3*eps) by linarith)
    dsimp [strictHeight]
    nlinarith
  have hbottom : strictHeight k (-l+3*eps) < 0 := by
    have harg : -l+3*eps < 0 := by dsimp [eps]; linarith
    dsimp [strictHeight]
    nlinarith [mul_nonneg hk.le (sq_nonneg (-l+3*eps))]
  have htarget : strictHeight k (-eps) < 0 := by
    dsimp [strictHeight]
    nlinarith [mul_nonneg hk.le (sq_nonneg (-eps))]
  refine ⟨h,eps,heps,hgap,(by linarith),hepsk,hmargin,hnear,?_⟩
  apply (div_lt_one (by linarith : 0 < strictHeight k (h+3*eps)-strictHeight k (-l+3*eps))).2
  linarith

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
