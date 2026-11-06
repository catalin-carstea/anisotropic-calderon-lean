import Calderon.ConnectionField
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic

open Set Metric
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def geodesicPhaseField (Q M : E → E →L[ℝ] E) : E × E → E × E :=
  fun p => (p.2,-coordinateConnectionField Q M p.1 p.2 p.2)

theorem contDiff_geodesicPhaseField (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) :
    ContDiff ℝ ∞ (geodesicPhaseField Q M) := by
  have hΓ := (contDiff_coordinateConnectionField_infty Q M hQ hM).comp
    (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : E × E → E))
  have hV := (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : E × E → E))
  exact hV.prodMk ((hΓ.clm_apply hV).clm_apply hV).neg

theorem exists_local_geodesic_phase (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (z₀ : E × E) (t₀ : ℝ) :
    ∃ a > (0:ℝ), ∃ ε > (0:ℝ), ∀ z ∈ closedBall z₀ a,
      ∃ α : ℝ → E × E, α t₀ = z ∧
        ∀ t ∈ Ioo (t₀-ε) (t₀+ε),
          HasDerivAt α (geodesicPhaseField Q M (α t)) t := by
  have hf : ContDiff ℝ 1 (geodesicPhaseField Q M) :=
    (contDiff_geodesicPhaseField Q M hQ hM).of_le (by simp)
  exact hf.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt t₀

theorem exists_local_coordinate_geodesic (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (x₀ v₀ : E) (t₀ : ℝ) :
    ∃ a > (0:ℝ), ∃ ε > (0:ℝ), ∀ z ∈ closedBall (x₀,v₀) a,
      ∃ q v : ℝ → E, q t₀ = z.1 ∧ v t₀ = z.2 ∧
        ∀ t ∈ Ioo (t₀-ε) (t₀+ε),
          HasDerivAt q (v t) t ∧
          HasDerivAt v (-coordinateConnectionField Q M (q t) (v t) (v t)) t := by
  obtain ⟨a,ha,ε,hε,hsol⟩ := exists_local_geodesic_phase Q M hQ hM (x₀,v₀) t₀
  refine ⟨a,ha,ε,hε,fun z hz => ?_⟩
  obtain ⟨α,hα,hα'⟩ := hsol z hz
  refine ⟨fun t => (α t).1,fun t => (α t).2,
    congrArg Prod.fst hα,congrArg Prod.snd hα,fun t ht => ?_⟩
  exact ⟨(hα' t ht).fst,(hα' t ht).snd⟩

#print axioms contDiff_geodesicPhaseField
#print axioms exists_local_coordinate_geodesic
end OAI.AnisotropicCalderon.ConnectionError
