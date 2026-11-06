import Calderon.MixedKernelConstruction.TaskInterface
import Mathlib.Tactic
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem coarse_closed_products_subset_fixedSeparation
    (B s0 s1 α : ℝ) (hB : 0 < B) (hs0 : 0 < s0) (hss : s0 ≤ s1)
    (hα : 0 < α) (hα4 : α ≤ 1/4) (p : R3) (hp : ‖p‖ ≤ B)
    (s : ℝ) (hs : s ∈ Icc s0 s1) :
    let η := s/20
    let c := p-η • EuclideanSpace.single (2:Fin 3) (1:ℝ)
    (closedBall c ((1-α/2)*η) ×ˢ {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s}
      ⊆ fixedSeparationSet (B+2*s1+1) (s0/4)) ∧
    (closedBall c (3*η) ×ˢ closedBall (p-s • EuclideanSpace.single (2:Fin 3) (1:ℝ)) (s/8)
      ⊆ fixedSeparationSet (B+2*s1+1) (s0/4)) := by
  dsimp only
  let e : R3 := EuclideanSpace.single (2:Fin 3) (1:ℝ)
  have he : ‖e‖ = 1 := by simp only [e,EuclideanSpace.norm_single,norm_one]
  have hspos : 0 < s := hs0.trans_le hs.1
  have hη : 0 < s/20 := by positivity
  have hShift : ‖(s/20) • e‖ = s/20 := by rw [norm_smul,he,Real.norm_eq_abs,abs_of_pos hη,mul_one]
  have hShiftS : ‖s • e‖ = s := by rw [norm_smul,he,Real.norm_eq_abs,abs_of_pos hspos,mul_one]
  have hXp (x : R3) (a : ℝ) (hx : x ∈ closedBall (p-(s/20) • e) a) : ‖x-p‖ ≤ a+s/20 := by
    have hxc : ‖x-(p-(s/20) • e)‖ ≤ a := by simpa only [mem_closedBall,dist_eq_norm] using hx
    calc
      ‖x-p‖ = ‖(x-(p-(s/20) • e))-(s/20) • e‖ := by congr 1; abel
      _ ≤ ‖x-(p-(s/20) • e)‖+‖(s/20) • e‖ := norm_sub_le _ _
      _ ≤ a+s/20 := by rw [hShift];linarith
  have hYp (y : R3) (hy : y ∈ closedBall (p-s • e) (s/8)) :
      7*s/8 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 9*s/8 := by
    have hyc : ‖y-(p-s • e)‖ ≤ s/8 := by simpa only [mem_closedBall,dist_eq_norm] using hy
    have h1 := norm_sub_le (y-(p-s • e)) (y-p)
    have hid : y-(p-s • e)-(y-p)=s • e := by abel
    rw [hid,hShiftS] at h1
    have h2 := norm_sub_le (y-(p-s • e)) (s • e)
    have hid2 : y-(p-s • e)-s • e=y-p := by abel
    rw [hid2,hShiftS] at h2
    constructor <;> linarith
  have hPair (x y : R3) (hx : ‖x-p‖ ≤ s/5) (hyL : s/2 ≤ ‖y-p‖) (hyU : ‖y-p‖ ≤ 2*s) :
      (x,y) ∈ fixedSeparationSet (B+2*s1+1) (s0/4) := by
    have hxn := norm_sub_norm_le x p
    have hyn := norm_sub_norm_le y p
    have hsep := norm_sub_le (y-x) (p-x)
    have hid : (y-x)-(p-x)=y-p := by abel
    rw [hid,norm_sub_rev p x,norm_sub_rev y x] at hsep
    refine ⟨by dsimp;linarith [hs.2],by dsimp;linarith [hs.2],?_⟩
    dsimp
    linarith [hs.1]
  constructor
  · rintro ⟨x,y⟩ ⟨hx,hyL,hyU⟩
    have hxp := hXp x ((1-α/2)*(s/20)) hx
    have hSmall : (1-α/2)*(s/20) ≤ s/20 := by nlinarith only [hα,hη]
    exact hPair x y (by linarith) hyL hyU
  · rintro ⟨x,y⟩ ⟨hx,hy⟩
    have hxp := hXp x (3*(s/20)) hx
    obtain ⟨hyL,hyU⟩ := hYp y hy
    exact hPair x y (by linarith) (by linarith) (by linarith)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
