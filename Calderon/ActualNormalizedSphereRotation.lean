import Calderon.WeightedSphereRotation
import Calderon.BoundedAngularShift

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualNormalizedSphereRotation
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularWeightedCore BoundedAngularShift SmoothSphereRotationProjection WeightedSphereRotation

/-- The actual degree-preserving rotation graph, including degree zero. -/
def sphereRotationGraph (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a b : Fin 3) : Submodule ℝ (SphereL2 × SphereL2) where
  carrier := {z | ∀ k, sphereHarmonicCoordinate hO hD k z.2 =
    harmonicSphereRotation k a b (sphereHarmonicCoordinate hO hD k z.1)}
  zero_mem' := by intro k; simp
  add_mem' := by
    intro z z' hz hz' k
    simp only [Prod.fst_add,Prod.snd_add,map_add]
    rw [hz k,hz' k]
  smul_mem' := by
    intro c z hz k
    change sphereHarmonicCoordinate hO hD k (c • z.2) =
      harmonicSphereRotation k a b (sphereHarmonicCoordinate hO hD k (c • z.1))
    rw [map_smul,map_smul,map_smul,hz k]

lemma sphereRotationGraph_output_unique (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (u v v' : SphereL2)
    (hv : (u,v) ∈ sphereRotationGraph hO hD a b)
    (hv' : (u,v') ∈ sphereRotationGraph hO hD a b) : v = v' := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  exact (hv k).trans (hv' k).symm

def rotationCoordinateSequence (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (u : SphereL2) :
    (k : ℕ) → harmonicSphereSubspace k :=
  fun k => harmonicSphereRotation k a b (sphereHarmonicCoordinate hO hD k u)

lemma exists_sphereRotationGraph_iff_summable (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (u : SphereL2) :
    (∃ v : SphereL2, (u,v) ∈ sphereRotationGraph hO hD a b) ↔
      Summable (fun k : ℕ =>
        ‖harmonicSphereRotation k a b (sphereHarmonicCoordinate hO hD k u)‖^2) := by
  constructor
  · rintro ⟨v,hv⟩
    have hs := (lp.memℓp (sphereHarmonicDecomposition hO hD v)).summable
      (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
    have he (k : ℕ) : sphereHarmonicCoordinate hO hD k v =
        harmonicSphereRotation k a b (sphereHarmonicCoordinate hO hD k u) := hv k
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,← sphereHarmonicCoordinate_apply,he] using hs
  · intro hs
    have hp : Memℓp (rotationCoordinateSequence hO hD a b u) 2 := by
      apply (memℓp_gen_iff (show 0 < (2 : ℝ≥0∞).toReal by norm_num)).mpr
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,rotationCoordinateSequence] using hs
    let q : lp (fun k : ℕ => harmonicSphereSubspace k) 2 :=
      ⟨rotationCoordinateSequence hO hD a b u,hp⟩
    refine ⟨(sphereHarmonicDecomposition hO hD).symm q,?_⟩
    intro k
    rw [sphereHarmonicCoordinate_apply,LinearIsometryEquiv.apply_symm_apply]
    rfl

lemma norm_sq_rotation_inverseDegree_coordinate_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (u : SphereL2) (k : ℕ) :
    ‖harmonicSphereRotation k a b
      (sphereHarmonicCoordinate hO hD k (inverseDegreeMultiplier hO hD u))‖^2 ≤
      2 * ‖sphereHarmonicCoordinate hO hD k u‖^2 := by
  have h := weighted_sq_harmonicSphereRotation_le 0 k a b
    (sphereHarmonicCoordinate hO hD k (inverseDegreeMultiplier hO hD u))
  have he : besselWeight 1 k^2 *
      ‖sphereHarmonicCoordinate hO hD k (inverseDegreeMultiplier hO hD u)‖^2 =
      ‖sphereHarmonicCoordinate hO hD k u‖^2 := by
    rw [inverseDegreeMultiplier_besselGraph hO hD u k,norm_smul,Real.norm_eq_abs,
      abs_of_pos (besselWeight_pos 1 k),mul_pow]
  simpa only [zero_add,besselWeight_zero_order,one_pow,one_mul,he] using h

lemma exists_normalizedRotation (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (u : SphereL2) :
    ∃ v : SphereL2, (inverseDegreeMultiplier hO hD u,v) ∈
      sphereRotationGraph hO hD a b := by
  apply (exists_sphereRotationGraph_iff_summable hO hD a b _).mpr
  have hs := (lp.memℓp (sphereHarmonicDecomposition hO hD u)).summable
    (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
  have hu : Summable (fun k : ℕ => ‖sphereHarmonicCoordinate hO hD k u‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,← sphereHarmonicCoordinate_apply] using hs
  exact Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (norm_sq_rotation_inverseDegree_coordinate_le hO hD a b u) (hu.mul_left (2:ℝ))

def normalizedRotationOutput (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (u : SphereL2) : SphereL2 :=
  (exists_normalizedRotation hO hD a b u).choose

lemma normalizedRotationOutput_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (u : SphereL2) :
    (inverseDegreeMultiplier hO hD u,normalizedRotationOutput hO hD a b u) ∈
      sphereRotationGraph hO hD a b :=
  (exists_normalizedRotation hO hD a b u).choose_spec

lemma normalizedRotationOutput_add (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (u v : SphereL2) :
    normalizedRotationOutput hO hD a b (u+v) =
      normalizedRotationOutput hO hD a b u + normalizedRotationOutput hO hD a b v := by
  apply sphereRotationGraph_output_unique hO hD a b (inverseDegreeMultiplier hO hD (u+v))
  · exact normalizedRotationOutput_graph hO hD a b (u+v)
  · have h := (sphereRotationGraph hO hD a b).add_mem
      (normalizedRotationOutput_graph hO hD a b u) (normalizedRotationOutput_graph hO hD a b v)
    change (inverseDegreeMultiplier hO hD u + inverseDegreeMultiplier hO hD v,
      normalizedRotationOutput hO hD a b u + normalizedRotationOutput hO hD a b v) ∈
        sphereRotationGraph hO hD a b at h
    rw [← map_add] at h
    exact h

lemma normalizedRotationOutput_smul (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (c : ℝ) (u : SphereL2) :
    normalizedRotationOutput hO hD a b (c • u) = c • normalizedRotationOutput hO hD a b u := by
  apply sphereRotationGraph_output_unique hO hD a b (inverseDegreeMultiplier hO hD (c • u))
  · exact normalizedRotationOutput_graph hO hD a b (c • u)
  · have h := (sphereRotationGraph hO hD a b).smul_mem c
      (normalizedRotationOutput_graph hO hD a b u)
    change (c • inverseDegreeMultiplier hO hD u,c • normalizedRotationOutput hO hD a b u) ∈
      sphereRotationGraph hO hD a b at h
    rw [← map_smul] at h
    exact h

lemma norm_normalizedRotationOutput_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (u : SphereL2) :
    ‖normalizedRotationOutput hO hD a b u‖ ≤ Real.sqrt 2 * ‖u‖ := by
  have h := norm_weighted_rotation_le hO hD 0 a b
    (inverseDegreeMultiplier hO hD u) u (normalizedRotationOutput hO hD a b u)
    (normalizedRotationOutput hO hD a b u)
    (by simpa using inverseDegreeMultiplier_besselGraph hO hD u)
    (normalizedRotationOutput_graph hO hD a b u)
    (sphereBesselGraph_zero_order hO hD _)
  exact h

/-- Actual R_ab W^-1, constructed on the genuine l2 decomposition. -/
def normalizedRotation (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a b : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
  LinearMap.mkContinuous
    ({ toFun := normalizedRotationOutput hO hD a b
       map_add' := normalizedRotationOutput_add hO hD a b
       map_smul' := normalizedRotationOutput_smul hO hD a b } : SphereL2 →ₗ[ℝ] SphereL2)
    (Real.sqrt 2) (norm_normalizedRotationOutput_le hO hD a b)

lemma norm_normalizedRotation_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) :
    ‖normalizedRotation hO hD a b‖ ≤ Real.sqrt 2 :=
  (normalizedRotation hO hD a b).opNorm_le_bound (Real.sqrt_nonneg _)
    (norm_normalizedRotationOutput_le hO hD a b)

lemma normalizedRotation_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (u U : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD 1) :
    (u,normalizedRotation hO hD a b U) ∈ sphereRotationGraph hO hD a b := by
  rw [← inverseDegreeMultiplier_of_besselGraph hO hD u U hU]
  exact normalizedRotationOutput_graph hO hD a b U

/-- Actual skew-adjunction at every degree, summed in the true Hilbert space. -/
lemma sphereRotationGraph_inner_skew (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (a b : Fin 3) (u ru v rv : SphereL2)
    (hru : (u,ru) ∈ sphereRotationGraph hO hD a b)
    (hrv : (v,rv) ∈ sphereRotationGraph hO hD a b) :
    ⟪ru,v⟫_ℝ = -⟪u,rv⟫_ℝ := by
  rw [inner_sphereHarmonicDecomposition hO hD ru v,
    inner_sphereHarmonicDecomposition hO hD u rv,← tsum_neg]
  apply tsum_congr
  intro k
  change ⟪sphereHarmonicCoordinate hO hD k ru,sphereHarmonicCoordinate hO hD k v⟫_ℝ =
    -⟪sphereHarmonicCoordinate hO hD k u,sphereHarmonicCoordinate hO hD k rv⟫_ℝ
  rw [hru k,hrv k]
  exact inner_harmonicSphereRotation_skew k a b _ _

end OAI.AnisotropicCalderon.ActualNormalizedSphereRotation
