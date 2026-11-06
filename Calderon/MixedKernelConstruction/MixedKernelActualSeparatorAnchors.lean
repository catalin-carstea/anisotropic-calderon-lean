import Calderon.MixedKernelConstruction.MixedKernelAnnulusGeometry
import Mathlib.Topology.Order.IntermediateValue
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter
open scoped ContDiff Topology

/-- ONE ceiling produces exact original separator points near every bounded limiting-plane point. -/
theorem exists_uniform_actual_separating_surface_anchors (S : KnownSideSourceData)
    (B eta a : ℝ) (hB : 0 < B) (heta : 0 < eta) (ha : 0 < a) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ p : R3, ‖p‖ ≤ B → p 2 = 0 →
        ∃ t ∈ Ioo (-eta) eta,
          ‖(p+t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))-p‖ < eta ∧
          lam • (p+t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) ∈ ball (0 : R3) a ∧
          S.separating_function (lam • (p+t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) = 0 := by
  let e : R3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have hen : ‖e‖ = 1 := by simp [e]
  have hden : 0 < 2*(B+eta+1) := by positivity
  obtain ⟨lE,hlE,HE⟩ := exists_uniform_scaled_separating_error S (B+eta+1) eta (by positivity) heta
  refine ⟨min lE (a/(2*(B+eta+1))),lt_min hlE (div_pos ha hden),
    fun lam hlam hsmall p hp hp2 => ?_⟩
  have hElam : lam ≤ lE := hsmall.trans (min_le_left _ _)
  have haBound : lam*(2*(B+eta+1)) ≤ a :=
    (le_div_iff₀ hden).mp (hsmall.trans (min_le_right _ _))
  have hnorm : ∀ t ∈ Icc (-eta) eta, ‖p+t • e‖ ≤ B+eta := by
    intro t ht
    have htabs : |t| ≤ eta := abs_le.mpr ht
    have hh := norm_add_le p (t • e)
    rw [norm_smul,Real.norm_eq_abs,hen,mul_one] at hh
    linarith
  have hcoord : ∀ t : ℝ, (p+t • e) 2 = t := by
    intro t
    simp [e,PiLp.add_apply,PiLp.smul_apply,hp2]
  let f : ℝ → ℝ := fun t => S.separating_function (lam • (p+t • e))
  have hpath : Continuous (fun t : ℝ => lam • (p+t • e)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).const_smul lam
  have hf : ContinuousOn f (Icc (-eta) eta) :=
    S.separating_function_smooth.continuousOn.comp hpath.continuousOn
      (fun t ht => (HE lam hlam hElam _ ((hnorm t ht).trans (by linarith))).1)
  have hleft : f (-eta) < 0 := by
    have hh := (HE lam hlam hElam _
      ((hnorm (-eta) ⟨le_rfl,by linarith⟩).trans (by linarith))).2.1
    rw [hcoord] at hh
    change |f (-eta)-lam*(-eta)| ≤ lam*eta/2 at hh
    have hpos := mul_pos hlam heta
    linarith [(abs_le.mp hh).2]
  have hright : 0 < f eta := by
    have hh := (HE lam hlam hElam _
      ((hnorm eta ⟨by linarith,le_rfl⟩).trans (by linarith))).2.1
    rw [hcoord] at hh
    change |f eta-lam*eta| ≤ lam*eta/2 at hh
    have hpos := mul_pos hlam heta
    linarith [(abs_le.mp hh).1]
  obtain ⟨t,ht,hzero⟩ := intermediate_value_Icc (by linarith : -eta ≤ eta) hf ⟨hleft.le,hright.le⟩
  have htlo : -eta < t := by
    rcases lt_or_eq_of_le ht.1 with h | h
    · exact h
    · rw [← h] at hzero
      linarith
  have hthi : t < eta := by
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact h
    · rw [h] at hzero
      linarith
  refine ⟨t,⟨htlo,hthi⟩,?_,?_,hzero⟩
  · change ‖(p+t • e)-p‖ < eta
    simpa only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,hen,mul_one] using abs_lt.mpr ⟨htlo,hthi⟩
  · rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hlam]
    have hh := mul_le_mul_of_nonneg_left (hnorm t ht) hlam.le
    have hpos : 0 < lam*(B+eta+1) := mul_pos hlam (by positivity)
    nlinarith

/-- The complete lower observed buffer remains in original W for the actual near-plane centers. -/
theorem exists_uniform_native_annulus_near_plane_lower_buffers (S : KnownSideSourceData)
    (B s0 s1 : ℝ) (hB : 0 < B) (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ p : R3, ‖p‖ ≤ B → p 2 ≤ s0/4 → ∀ s ∈ Icc s0 s1,
        ∀ y ∈ closedBall (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8),
          lam • y ∈ S.W := by
  have hs1 : 0 < s1 := hs0.trans_le hss
  obtain ⟨lam0,hpos,H⟩ := exists_uniform_scaled_lower_strip S (B+2*s1+1) (s0/2)
    (by positivity) (half_pos hs0)
  refine ⟨lam0,hpos,fun lam hlam hsmall p hp hp2 s hs y hy => ?_⟩
  have hspos : 0 < s := hs0.trans_le hs.1
  let c := p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have hyc : ‖y-c‖ ≤ s/8 := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hc : ‖c‖ ≤ ‖p‖+s := by
    have hh := norm_sub_le p (s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    simpa [c,norm_smul,Real.norm_eq_abs,abs_of_pos hspos] using hh
  have hnorm : ‖y‖ ≤ B+2*s1+1 := by
    have hh := norm_add_le (y-c) c
    rw [sub_add_cancel] at hh
    linarith [hs.2]
  have hcoord : (y-c) 2 ≤ ‖y-c‖ := (abs_le.mp (abs_coord_le_norm (y-c) 2)).2
  have hc2 : c 2 = p 2-s := by simp [c,PiLp.sub_apply,PiLp.smul_apply]
  have hsum : y 2 = (y-c) 2+c 2 := by simp only [PiLp.sub_apply]; ring
  have hheight : y 2 ≤ -(s0/2) := by linarith [hs.1]
  exact H lam hlam hsmall y hnorm hheight


end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
