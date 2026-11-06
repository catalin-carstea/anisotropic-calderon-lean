import Calderon.SpectralCoreRegularity
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SpectralWeightedGraph
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity

lemma sphereHarmonicCoordinate_partialSum
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (n k : ℕ) (u : SphereL2) :
    sphereHarmonicCoordinate hO hD k (sphereHarmonicPartialSum hO hD n u) =
      if k < n then sphereHarmonicCoordinate hO hD k u else 0 := by
  classical
  rw [sphereHarmonicPartialSum_apply,map_sum]
  by_cases hk : k < n
  · rw [ite_eq_left hk,Finset.sum_eq_single k]
    · exact sphereHarmonicCoordinate_subtype hO hD k _
    · intro j _ hj
      simp [sphereHarmonicCoordinate_apply,sphereHarmonicDecomposition_subtype,
        lp.single_apply,Ne.symm hj]
    · intro hknot
      exact (hknot (Finset.mem_range.mpr hk)).elim
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : k ≠ j := by intro he; subst j; exact hk (Finset.mem_range.mp hj)
    simp [sphereHarmonicCoordinate_apply,sphereHarmonicDecomposition_subtype,
      lp.single_apply,hjk]

def spectralGraph (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : ℕ → ℝ) : Submodule ℝ (SphereL2 × SphereL2) where
  carrier := {z | ∀ k, sphereHarmonicCoordinate hO hD k z.2 =
    w k • sphereHarmonicCoordinate hO hD k z.1}
  zero_mem' := by intro k; simp
  add_mem' := by
    intro z z' hz hz' k
    simp only [Prod.fst_add,Prod.snd_add,map_add,smul_add]
    rw [hz k,hz' k]
  smul_mem' := by
    intro c z hz k
    change sphereHarmonicCoordinate hO hD k (c • z.2) =
      w k • sphereHarmonicCoordinate hO hD k (c • z.1)
    rw [map_smul,map_smul]
    rw [hz k,smul_comm]

lemma mem_spectralGraph_iff (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (u v : SphereL2) :
    (u,v) ∈ spectralGraph hO hD w ↔ ∀ k,
      sphereHarmonicCoordinate hO hD k v =
        w k • sphereHarmonicCoordinate hO hD k u := Iff.rfl

theorem spectralGraph_output_unique (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (u v v' : SphereL2)
    (hv : (u,v) ∈ spectralGraph hO hD w)
    (hv' : (u,v') ∈ spectralGraph hO hD w) : v = v' := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  exact (hv k).trans (hv' k).symm

lemma spectralGraph_zero_input (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (v : SphereL2)
    (hv : (0,v) ∈ spectralGraph hO hD w) : v = 0 :=
  spectralGraph_output_unique hO hD w 0 v 0 hv (spectralGraph hO hD w).zero_mem

theorem isClosed_spectralGraph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) :
    IsClosed (spectralGraph hO hD w : Set (SphereL2 × SphereL2)) := by
  change IsClosed {z : SphereL2 × SphereL2 | ∀ k,
    sphereHarmonicCoordinate hO hD k z.2 = w k • sphereHarmonicCoordinate hO hD k z.1}
  simp_rw [ofPred_forall]
  apply isClosed_iInter
  intro k
  exact isClosed_eq ((sphereHarmonicCoordinate hO hD k).continuous.comp continuous_snd)
    (((sphereHarmonicCoordinate hO hD k).continuous.comp continuous_fst).const_smul (w k))

lemma spectralGraph_partialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (z : SphereL2 × SphereL2)
    (hz : z ∈ spectralGraph hO hD w) (n : ℕ) :
    (sphereHarmonicPartialSum hO hD n z.1,sphereHarmonicPartialSum hO hD n z.2) ∈
      spectralGraph hO hD w := by
  intro k
  simp_rw [sphereHarmonicCoordinate_partialSum]
  by_cases hk : k < n
  · simpa only [if_pos hk] using hz k
  · simp only [if_neg hk,smul_zero]

def spectralFiniteGraph (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : ℕ → ℝ) : Set (SphereL2 × SphereL2) :=
  {z | z ∈ spectralGraph hO hD w ∧ ∃ n : ℕ, ∀ k : ℕ, n ≤ k →
    sphereHarmonicCoordinate hO hD k z.1 = 0 ∧
    sphereHarmonicCoordinate hO hD k z.2 = 0}

lemma spectralFiniteGraph_partialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (z : SphereL2 × SphereL2)
    (hz : z ∈ spectralGraph hO hD w) (n : ℕ) :
    (sphereHarmonicPartialSum hO hD n z.1,sphereHarmonicPartialSum hO hD n z.2) ∈
      spectralFiniteGraph hO hD w := by
  refine ⟨spectralGraph_partialSum hO hD w z hz n,n,?_⟩
  intro k hk
  simp only [sphereHarmonicCoordinate_partialSum,if_neg (not_lt.mpr hk),and_self]

theorem tendsto_spectralGraph_partialSum (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (z : SphereL2 × SphereL2) :
    Tendsto (fun n : ℕ =>
      (sphereHarmonicPartialSum hO hD n z.1,sphereHarmonicPartialSum hO hD n z.2))
      atTop (𝓝 z) :=
  (tendsto_sphereHarmonicPartialSum hO hD z.1).prodMk_nhds
    (tendsto_sphereHarmonicPartialSum hO hD z.2)

theorem closure_spectralFiniteGraph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) :
    closure (spectralFiniteGraph hO hD w) =
      (spectralGraph hO hD w : Set (SphereL2 × SphereL2)) := by
  apply Subset.antisymm
  · exact closure_minimal (fun _ hz => hz.1) (isClosed_spectralGraph hO hD w)
  · intro z hz
    exact isClosed_closure.mem_of_tendsto (tendsto_spectralGraph_partialSum hO hD z)
      (Eventually.of_forall (fun n => subset_closure (spectralFiniteGraph_partialSum hO hD w z hz n)))

theorem norm_sq_spectralGraph_output (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (u v : SphereL2)
    (hv : (u,v) ∈ spectralGraph hO hD w) :
    ‖v‖ ^ 2 = ∑' k : ℕ, |w k| ^ 2 * ‖sphereHarmonicCoordinate hO hD k u‖ ^ 2 := by
  rw [norm_sq_sphereHarmonicDecomposition hO hD v]
  apply tsum_congr
  intro k
  change ‖sphereHarmonicCoordinate hO hD k v‖ ^ 2 = _
  rw [hv k,norm_smul,Real.norm_eq_abs,mul_pow]

def besselWeight (s : ℝ) (k : ℕ) : ℝ := (1 + (k : ℝ)) ^ s

lemma besselWeight_pos (s : ℝ) (k : ℕ) : 0 < besselWeight s k :=
  Real.rpow_pos_of_pos (by positivity) s

lemma besselWeight_zero_degree (s : ℝ) : besselWeight s 0 = 1 := by
  simp [besselWeight]

lemma besselWeight_zero_order (k : ℕ) : besselWeight 0 k = 1 := by
  simp [besselWeight]

def sphereBesselGraph (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) : Submodule ℝ (SphereL2 × SphereL2) := spectralGraph hO hD (besselWeight s)

theorem isClosed_sphereBesselGraph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) :
    IsClosed (sphereBesselGraph hO hD s : Set (SphereL2 × SphereL2)) :=
  isClosed_spectralGraph hO hD (besselWeight s)

lemma inner_sphereHarmonicCoordinate_right (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (u : SphereL2) (a : harmonicSphereSubspace k) :
    ⟪u,(a : SphereL2)⟫_ℝ = ⟪sphereHarmonicCoordinate hO hD k u,a⟫_ℝ := by
  rw [← (sphereHarmonicDecomposition hO hD).inner_map_map,
    sphereHarmonicDecomposition_subtype]
  exact lp.inner_single_right (𝕜 := ℝ) k a (sphereHarmonicDecomposition hO hD u)

theorem spectralGraph_inner_symm (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (u v a b : SphereL2)
    (huv : (u,v) ∈ spectralGraph hO hD w)
    (hab : (a,b) ∈ spectralGraph hO hD w) : ⟪v,a⟫_ℝ = ⟪u,b⟫_ℝ := by
  rw [inner_sphereHarmonicDecomposition hO hD v a,
    inner_sphereHarmonicDecomposition hO hD u b]
  apply tsum_congr
  intro k
  change ⟪sphereHarmonicCoordinate hO hD k v,sphereHarmonicCoordinate hO hD k a⟫_ℝ =
    ⟪sphereHarmonicCoordinate hO hD k u,sphereHarmonicCoordinate hO hD k b⟫_ℝ
  rw [huv k,hab k]
  change ⟪w k • sphereHarmonicCoordinate hO hD k u,
      sphereHarmonicCoordinate hO hD k a⟫_ℝ =
    ⟪sphereHarmonicCoordinate hO hD k u,w k • sphereHarmonicCoordinate hO hD k a⟫_ℝ
  rw [real_inner_smul_left (sphereHarmonicCoordinate hO hD k u)
      (sphereHarmonicCoordinate hO hD k a) (w k),
    real_inner_smul_right (sphereHarmonicCoordinate hO hD k u)
      (sphereHarmonicCoordinate hO hD k a) (w k)]

lemma spectralGraph_single (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (k : ℕ) (a : harmonicSphereSubspace k) :
    ((a : SphereL2),w k • (a : SphereL2)) ∈ spectralGraph hO hD w := by
  intro j
  simp only [map_smul,sphereHarmonicCoordinate_apply,sphereHarmonicDecomposition_subtype]
  by_cases hj : j = k
  · subst j; simp
  · simp [lp.single_apply,hj,Ne.symm hj]

lemma spectralFiniteGraph_single (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (k : ℕ) (a : harmonicSphereSubspace k) :
    ((a : SphereL2),w k • (a : SphereL2)) ∈ spectralFiniteGraph hO hD w := by
  refine ⟨spectralGraph_single hO hD w k a,k+1,?_⟩
  intro j hj
  have hjk : j ≠ k := by omega
  simp [sphereHarmonicCoordinate_apply,sphereHarmonicDecomposition_subtype,
    map_smul,lp.single_apply,hjk,Ne.symm hjk]

theorem mem_spectralGraph_iff_inner_finite (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (u v : SphereL2) :
    (u,v) ∈ spectralGraph hO hD w ↔ ∀ z ∈ spectralFiniteGraph hO hD w,
      ⟪v,z.1⟫_ℝ = ⟪u,z.2⟫_ℝ := by
  constructor
  · intro huv z hz
    exact spectralGraph_inner_symm hO hD w u v z.1 z.2 huv hz.1
  · intro ht k
    let q : harmonicSphereSubspace k :=
      sphereHarmonicCoordinate hO hD k v - w k • sphereHarmonicCoordinate hO hD k u
    have he := ht ((q : SphereL2),w k • (q : SphereL2))
      (spectralFiniteGraph_single hO hD w k q)
    change ⟪v,(q : SphereL2)⟫_ℝ = ⟪u,w k • (q : SphereL2)⟫_ℝ at he
    rw [real_inner_smul_right,inner_sphereHarmonicCoordinate_right hO hD k,
      inner_sphereHarmonicCoordinate_right hO hD k] at he
    have hq : ⟪q,q⟫_ℝ = 0 := by
      dsimp only [q]
      rw [inner_sub_left,real_inner_smul_left (sphereHarmonicCoordinate hO hD k u)
        (sphereHarmonicCoordinate hO hD k v - w k • sphereHarmonicCoordinate hO hD k u) (w k)]
      exact sub_eq_zero.mpr he
    have hz : q = 0 := (inner_self_eq_zero).mp hq
    exact sub_eq_zero.mp hz

theorem mem_spectralGraph_iff_inner_all (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (u v : SphereL2) :
    (u,v) ∈ spectralGraph hO hD w ↔ ∀ z ∈ spectralGraph hO hD w,
      ⟪v,z.1⟫_ℝ = ⟪u,z.2⟫_ℝ := by
  constructor
  · intro huv z hz
    exact spectralGraph_inner_symm hO hD w u v z.1 z.2 huv hz
  · intro ht
    apply (mem_spectralGraph_iff_inner_finite hO hD w u v).mpr
    intro z hz
    exact ht z hz.1

def spectralCoordinateSequence (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (u : SphereL2) :
    (k : ℕ) → harmonicSphereSubspace k :=
  fun k => w k • sphereHarmonicCoordinate hO hD k u

theorem memLp_spectralCoordinateSequence_iff (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (u : SphereL2) :
    Memℓp (spectralCoordinateSequence hO hD w u) 2 ↔
      Summable (fun k : ℕ => |w k| ^ 2 * ‖sphereHarmonicCoordinate hO hD k u‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,spectralCoordinateSequence,
    norm_smul,Real.norm_eq_abs,mul_pow] using
    (memℓp_gen_iff (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
      (f := spectralCoordinateSequence hO hD w u))

theorem exists_spectralGraph_iff_summable (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (u : SphereL2) :
    (∃ v : SphereL2, (u,v) ∈ spectralGraph hO hD w) ↔
      Summable (fun k : ℕ => |w k| ^ 2 * ‖sphereHarmonicCoordinate hO hD k u‖ ^ 2) := by
  constructor
  · rintro ⟨v,hv⟩
    apply (memLp_spectralCoordinateSequence_iff hO hD w u).mp
    have he : spectralCoordinateSequence hO hD w u =
        (sphereHarmonicDecomposition hO hD v : (k : ℕ) → harmonicSphereSubspace k) := by
      funext k
      exact (hv k).symm
    rw [he]
    exact lp.memℓp _
  · intro hs
    let q : lp (fun k : ℕ => harmonicSphereSubspace k) 2 :=
      ⟨spectralCoordinateSequence hO hD w u,
        (memLp_spectralCoordinateSequence_iff hO hD w u).mpr hs⟩
    refine ⟨(sphereHarmonicDecomposition hO hD).symm q,?_⟩
    intro k
    rw [sphereHarmonicCoordinate_apply,LinearIsometryEquiv.apply_symm_apply]
    rfl

theorem hasSum_spectralGraph_output (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (u v : SphereL2)
    (hv : (u,v) ∈ spectralGraph hO hD w) :
    HasSum (fun k : ℕ => w k • (sphereHarmonicCoordinate hO hD k u : SphereL2)) v := by
  have he : (fun k : ℕ => w k • (sphereHarmonicCoordinate hO hD k u : SphereL2)) =
      (fun k : ℕ => (sphereHarmonicDecomposition hO hD v k : SphereL2)) := by
    funext k
    exact congrArg (fun a : harmonicSphereSubspace k => (a : SphereL2)) (hv k).symm
  rw [he]
  exact hasSum_sphereHarmonicDecomposition hO hD v

end OAI.AnisotropicCalderon.SpectralWeightedGraph
