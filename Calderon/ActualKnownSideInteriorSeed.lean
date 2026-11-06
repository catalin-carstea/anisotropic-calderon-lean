import Calderon.MixedKernelConstruction.TaskInterface
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem zero_mem_interior_cylinder : (0 : R3) ∈ interior cylinder := by
  let O : Set R3 := {z | z 0 ^ 2 + z 1 ^ 2 < 1 ∧ (-1 : ℝ) < z 2 ∧ z 2 < 1}
  have hc (i : Fin 3) : Continuous (fun z : R3 => z i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  have hO : IsOpen O := (isOpen_lt ((hc 0).pow 2 |>.add ((hc 1).pow 2))
      continuous_const).inter
    ((isOpen_lt continuous_const (hc 2)).inter (isOpen_lt (hc 2) continuous_const))
  have hSub : O ⊆ cylinder := by
    rintro z ⟨hxy,hlo,hhi⟩
    exact ⟨hxy.le,hlo.le,hhi.le⟩
  exact interior_maximal hSub hO (by norm_num [O])

theorem known_side_seed_nonempty_in_open_neighborhood
    (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam)
    (V : Set R3) (hV : IsOpen V) (h0V : (0 : R3) ∈ V) :
    (V ∩ (fun y : R3 => lam • y) ⁻¹' S.W).Nonempty := by
  rcases S.one_sided_room with ⟨a,ha,_,hNeg⟩
  let U : Set R3 := (fun x : R3 => lam⁻¹ • x) ⁻¹' V ∩ ball (0 : R3) a
  have hScale : Continuous (fun x : R3 => lam⁻¹ • x) :=
    (lam⁻¹ • ContinuousLinearMap.id ℝ R3).continuous
  have hU : IsOpen U := by
    change IsOpen ((fun x : R3 => lam⁻¹ • x) ⁻¹' V ∩ ball (0 : R3) a)
    exact (hV.preimage hScale).inter isOpen_ball
  have h0U : (0 : R3) ∈ U := by
    constructor
    · simpa only [mem_preimage,smul_zero] using h0V
    · exact mem_ball_self ha
  by_contra hEmpty
  have hMin : IsLocalMin S.separating_function (0 : R3) := by
    change ∀ᶠ x in 𝓝 (0 : R3), S.separating_function 0 ≤ S.separating_function x
    filter_upwards [hU.mem_nhds h0U] with x hx
    rw [S.separating_function_zero]
    by_contra hn
    have hnx : S.separating_function x < 0 := lt_of_not_ge hn
    apply hEmpty
    refine ⟨lam⁻¹ • x,hx.1,?_⟩
    change lam • (lam⁻¹ • x) ∈ S.W
    rw [smul_smul,mul_inv_cancel₀ hlam.ne',one_smul]
    exact hNeg ⟨hx.2,hnx⟩
  have hOne : fderiv ℝ S.separating_function (0 : R3)
      (EuclideanSpace.single (2 : Fin 3) 1) = 1 := by
    simpa using S.separating_function_normal (EuclideanSpace.single (2 : Fin 3) 1)
  rw [hMin.fderiv_eq_zero] at hOne
  norm_num at hOne

theorem known_side_seed_nonempty_in_interior_cylinder
    (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam) :
    (interior cylinder ∩ (fun y : R3 => lam • y) ⁻¹' S.W).Nonempty :=
  known_side_seed_nonempty_in_open_neighborhood S lam hlam (interior cylinder)
    isOpen_interior zero_mem_interior_cylinder

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
