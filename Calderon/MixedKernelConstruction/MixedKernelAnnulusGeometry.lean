import Calderon.MixedKernelConstruction.MixedKernelUniformLowerSide
import Mathlib.Analysis.Normed.Module.Connected
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter
open scoped ContDiff Topology

theorem isOpen_native_annulus (p : R3) (r R : ℝ) :
    IsOpen {y : R3 | r < ‖y-p‖ ∧ ‖y-p‖ < R} :=
  (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)

/-- The actual three-dimensional annulus is connected, via its sphere-times-radius parametrization. -/
theorem isConnected_native_annulus (p : R3) (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    IsConnected {y : R3 | r < ‖y-p‖ ∧ ‖y-p‖ < R} := by
  have hdim : 1 < Module.rank ℝ R3 := by
    rw [← Module.finrank_eq_rank]
    norm_num [R3]
  have hS : IsConnected (sphere (0 : R3) 1) := isConnected_sphere hdim _ (by norm_num)
  have hI : IsConnected (Ioo r R) := isConnected_Ioo hrR
  let f : R3 × ℝ → R3 := fun z => p+z.2 • z.1
  have hcont : Continuous f := continuous_const.add (continuous_snd.smul continuous_fst)
  have himage : f '' (sphere (0 : R3) 1 ×ˢ Ioo r R) =
      {y : R3 | r < ‖y-p‖ ∧ ‖y-p‖ < R} := by
    ext y
    constructor
    · rintro ⟨⟨v,t⟩,⟨hv,ht⟩,rfl⟩
      have hvn : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
      have ht0 : 0 < t := hr.trans ht.1
      simpa only [mem_setOf_eq,mem_Ioo,f,add_sub_cancel_left,norm_smul,
        Real.norm_eq_abs,abs_of_pos ht0,hvn,mul_one] using ht
    · intro hy
      have hn : 0 < ‖y-p‖ := hr.trans hy.1
      refine ⟨(‖y-p‖⁻¹ • (y-p),‖y-p‖),⟨?_,hy⟩,?_⟩
      · rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
      · dsimp [f]
        rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul,add_sub_cancel]
  rw [← himage]
  exact (hS.prod hI).image f hcont.continuousOn

theorem isCompact_native_closed_annulus (p : R3) (r R : ℝ) :
    IsCompact {y : R3 | r ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ R} := by
  have hset : {y : R3 | r ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ R} = closedBall p R \ ball p r := by
    ext y
    simp only [mem_setOf_eq,mem_diff,mem_closedBall,mem_ball,dist_eq_norm,not_lt]
    exact and_comm
  rw [hset]
  exact (isCompact_closedBall p R).diff isOpen_ball

/-- The whole CLOSED lower observation buffer stays strictly inside the large separated annulus. -/
theorem native_closed_observation_subset_annulus (p : R3) (s : ℝ) (hs : 0 < s) :
    closedBall (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8) ⊆
      {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} := by
  let c := p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have hcp : dist c p = s := by
    have heq : c-p = -(s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
      dsimp [c]
      abel
    rw [dist_eq_norm,heq,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    simp
  intro y hy
  have hyc : dist y c ≤ s/8 := mem_closedBall.mp hy
  have hlow := dist_triangle c y p
  have hhigh := dist_triangle y c p
  rw [hcp,dist_comm c y,dist_eq_norm y p] at hlow
  rw [hcp,dist_eq_norm y p] at hhigh
  constructor <;> linarith

/-- ONE original known-side ceiling works for the entire compact range of centers and scales. -/
theorem exists_uniform_native_annulus_lower_buffers (S : KnownSideSourceData)
    (B s0 s1 : ℝ) (hB : 0 < B) (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ p : R3, ‖p‖ ≤ B → p 2 = 0 → ∀ s ∈ Icc s0 s1,
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
  have hc2 : c 2 = -s := by simp [c,PiLp.sub_apply,PiLp.smul_apply,hp2]
  have hsum : y 2 = (y-c) 2+c 2 := by simp only [PiLp.sub_apply]; ring
  have hheight : y 2 ≤ -(s0/2) := by linarith [hs.1]
  exact H lam hlam hsmall y hnorm hheight

/-- Actual output/compact margins around every point at the prescribed separation scale. -/
theorem native_annulus_target_geometry (p : R3) (s : ℝ) (hs : 0 < s) :
    IsOpen {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} ∧
    IsConnected {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} ∧
    IsOpen {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5} ∧
    IsConnected {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5} ∧
    IsCompact {y : R3 | 3*s/4 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 5*s/4} ∧
    {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5} ⊆
      {y : R3 | 3*s/4 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 5*s/4} ∧
    {y : R3 | 3*s/4 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 5*s/4} ⊆
      {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} ∧
    ∀ y : R3, ‖y-p‖ = s → 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5 := by
  refine ⟨isOpen_native_annulus _ _ _,isConnected_native_annulus _ _ _ (by positivity) (by linarith),
    isOpen_native_annulus _ _ _,isConnected_native_annulus _ _ _ (by positivity) (by linarith),
    isCompact_native_closed_annulus _ _ _,?_,?_,?_⟩
  · intro y hy
    constructor <;> linarith [hy.1,hy.2]
  · intro y hy
    constructor <;> linarith [hy.1,hy.2]
  · intro y hy
    constructor <;> linarith

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
