import Calderon.AngularWeightedCore
import Calderon.BoundedSpectralMultiplier

set_option autoImplicit false
noncomputable section
open scoped Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.BoundedAngularShift
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SpectralWeightedGraph AngularShiftGraph AngularWeightedCore BoundedSpectralMultiplier

def inverseDegreeWeight (k : ℕ) : ℝ := (1+(k:ℝ))⁻¹

lemma abs_inverseDegreeWeight_le_one (k : ℕ) : |inverseDegreeWeight k| ≤ 1 := by
  have hk : (1:ℝ) ≤ 1+(k:ℝ) := by
    linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))]
  rw [inverseDegreeWeight,abs_of_pos (inv_pos.mpr (by positivity))]
  exact (inv_le_one₀ (by positivity)).mpr hk

/-- The bounded inverse of the exact source Sobolev weight 1+B. -/
def inverseDegreeMultiplier (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    SphereL2 →L[ℝ] SphereL2 :=
  boundedSpectralMultiplier hO hD inverseDegreeWeight 1 (by norm_num)
    abs_inverseDegreeWeight_le_one

lemma inverseDegreeMultiplier_coordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) (k : ℕ) :
    sphereHarmonicCoordinate hO hD k (inverseDegreeMultiplier hO hD u) =
      inverseDegreeWeight k • sphereHarmonicCoordinate hO hD k u :=
  boundedSpectralMultiplier_mem hO hD inverseDegreeWeight 1 (by norm_num)
    abs_inverseDegreeWeight_le_one u k

lemma inverseDegreeMultiplier_besselGraph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    (inverseDegreeMultiplier hO hD u,u) ∈ sphereBesselGraph hO hD 1 := by
  intro k
  rw [inverseDegreeMultiplier_coordinate,smul_smul]
  simp [besselWeight,inverseDegreeWeight,Real.rpow_one,
    show (1+(k:ℝ)) ≠ 0 by positivity]

lemma inverseDegreeMultiplier_of_besselGraph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u w : SphereL2)
    (hw : (u,w) ∈ sphereBesselGraph hO hD 1) :
    inverseDegreeMultiplier hO hD w = u := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k (inverseDegreeMultiplier hO hD w) =
    sphereHarmonicCoordinate hO hD k u
  rw [inverseDegreeMultiplier_coordinate,hw k,smul_smul]
  simp [besselWeight,inverseDegreeWeight,Real.rpow_one,
    show (1+(k:ℝ)) ≠ 0 by positivity]

lemma sphereBesselGraph_zero_order (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    (u,u) ∈ sphereBesselGraph hO hD 0 := by
  intro k
  simp only [besselWeight_zero_order,one_smul]

lemma exists_normalizedDerivative (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) :
    ∃ v : SphereL2, (inverseDegreeMultiplier hO hD u,v) ∈
      sphereDerivativeGraph hF hO hD i := by
  obtain ⟨v,hv,_⟩ := exists_sphereDerivativeGraph_hasWeight hF hO hD i 0 (by norm_num)
    (inverseDegreeMultiplier hO hD u)
    ⟨u,by simpa using inverseDegreeMultiplier_besselGraph hO hD u⟩
  exact ⟨v,hv⟩

lemma exists_normalizedRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) :
    ∃ v : SphereL2, (inverseDegreeMultiplier hO hD u,v) ∈
      sphereRaisingGraph hF hO hD i := by
  obtain ⟨v,hv,_⟩ := exists_sphereRaisingGraph_hasWeight hF hO hD i 0 (by norm_num)
    (inverseDegreeMultiplier hO hD u)
    ⟨u,by simpa using inverseDegreeMultiplier_besselGraph hO hD u⟩
  exact ⟨v,hv⟩

def normalizedDerivativeOutput (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) : SphereL2 := (exists_normalizedDerivative hF hO hD i u).choose

def normalizedRaisingOutput (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) : SphereL2 := (exists_normalizedRaising hF hO hD i u).choose

lemma normalizedDerivativeOutput_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) :
    (inverseDegreeMultiplier hO hD u,normalizedDerivativeOutput hF hO hD i u) ∈
      sphereDerivativeGraph hF hO hD i :=
  (exists_normalizedDerivative hF hO hD i u).choose_spec

lemma normalizedRaisingOutput_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) :
    (inverseDegreeMultiplier hO hD u,normalizedRaisingOutput hF hO hD i u) ∈
      sphereRaisingGraph hF hO hD i :=
  (exists_normalizedRaising hF hO hD i u).choose_spec

lemma normalizedDerivativeOutput_add (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u v : SphereL2) :
    normalizedDerivativeOutput hF hO hD i (u+v) =
      normalizedDerivativeOutput hF hO hD i u + normalizedDerivativeOutput hF hO hD i v := by
  apply sphereDerivativeGraph_output_unique hF hO hD i (inverseDegreeMultiplier hO hD (u+v))
  · exact normalizedDerivativeOutput_graph hF hO hD i (u+v)
  · have h := (sphereDerivativeGraph hF hO hD i).add_mem
      (normalizedDerivativeOutput_graph hF hO hD i u)
      (normalizedDerivativeOutput_graph hF hO hD i v)
    change (inverseDegreeMultiplier hO hD u + inverseDegreeMultiplier hO hD v,
      normalizedDerivativeOutput hF hO hD i u + normalizedDerivativeOutput hF hO hD i v) ∈
        sphereDerivativeGraph hF hO hD i at h
    rw [← map_add] at h
    exact h

lemma normalizedRaisingOutput_add (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u v : SphereL2) :
    normalizedRaisingOutput hF hO hD i (u+v) =
      normalizedRaisingOutput hF hO hD i u + normalizedRaisingOutput hF hO hD i v := by
  apply sphereRaisingGraph_output_unique hF hO hD i (inverseDegreeMultiplier hO hD (u+v))
  · exact normalizedRaisingOutput_graph hF hO hD i (u+v)
  · have h := (sphereRaisingGraph hF hO hD i).add_mem
      (normalizedRaisingOutput_graph hF hO hD i u)
      (normalizedRaisingOutput_graph hF hO hD i v)
    change (inverseDegreeMultiplier hO hD u + inverseDegreeMultiplier hO hD v,
      normalizedRaisingOutput hF hO hD i u + normalizedRaisingOutput hF hO hD i v) ∈
        sphereRaisingGraph hF hO hD i at h
    rw [← map_add] at h
    exact h

lemma normalizedDerivativeOutput_smul (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (c : ℝ) (u : SphereL2) :
    normalizedDerivativeOutput hF hO hD i (c • u) =
      c • normalizedDerivativeOutput hF hO hD i u := by
  apply sphereDerivativeGraph_output_unique hF hO hD i (inverseDegreeMultiplier hO hD (c • u))
  · exact normalizedDerivativeOutput_graph hF hO hD i (c • u)
  · have h := (sphereDerivativeGraph hF hO hD i).smul_mem c
      (normalizedDerivativeOutput_graph hF hO hD i u)
    change (c • inverseDegreeMultiplier hO hD u,
      c • normalizedDerivativeOutput hF hO hD i u) ∈ sphereDerivativeGraph hF hO hD i at h
    rw [← map_smul] at h
    exact h

lemma normalizedRaisingOutput_smul (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (c : ℝ) (u : SphereL2) :
    normalizedRaisingOutput hF hO hD i (c • u) =
      c • normalizedRaisingOutput hF hO hD i u := by
  apply sphereRaisingGraph_output_unique hF hO hD i (inverseDegreeMultiplier hO hD (c • u))
  · exact normalizedRaisingOutput_graph hF hO hD i (c • u)
  · have h := (sphereRaisingGraph hF hO hD i).smul_mem c
      (normalizedRaisingOutput_graph hF hO hD i u)
    change (c • inverseDegreeMultiplier hO hD u,
      c • normalizedRaisingOutput hF hO hD i u) ∈ sphereRaisingGraph hF hO hD i at h
    rw [← map_smul] at h
    exact h

lemma norm_normalizedDerivativeOutput_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) : ‖normalizedDerivativeOutput hF hO hD i u‖ ≤ 2 * ‖u‖ := by
  have h := norm_sq_weighted_derivative_le hF hO hD i 0 (by norm_num)
    (inverseDegreeMultiplier hO hD u) u
    (normalizedDerivativeOutput hF hO hD i u) (normalizedDerivativeOutput hF hO hD i u)
    (by simpa using inverseDegreeMultiplier_besselGraph hO hD u)
    (normalizedDerivativeOutput_graph hF hO hD i u)
    (sphereBesselGraph_zero_order hO hD _)
  nlinarith [norm_nonneg (normalizedDerivativeOutput hF hO hD i u),norm_nonneg u]

lemma norm_normalizedRaisingOutput_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) : ‖normalizedRaisingOutput hF hO hD i u‖ ≤ 2 * ‖u‖ := by
  have h := norm_sq_weighted_raising_le hF hO hD i 0 (by norm_num)
    (inverseDegreeMultiplier hO hD u) u
    (normalizedRaisingOutput hF hO hD i u) (normalizedRaisingOutput hF hO hD i u)
    (by simpa using inverseDegreeMultiplier_besselGraph hO hD u)
    (normalizedRaisingOutput_graph hF hO hD i u)
    (sphereBesselGraph_zero_order hO hD _)
  norm_num at h
  nlinarith [norm_nonneg (normalizedRaisingOutput hF hO hD i u),norm_nonneg u]

/-- Genuine A_i (1+B)^{-1}, constructed from exact coordinates and their proved estimate. -/
def normalizedDerivative (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
  LinearMap.mkContinuous
    ({ toFun := normalizedDerivativeOutput hF hO hD i
       map_add' := normalizedDerivativeOutput_add hF hO hD i
       map_smul' := normalizedDerivativeOutput_smul hF hO hD i } : SphereL2 →ₗ[ℝ] SphereL2)
    2 (norm_normalizedDerivativeOutput_le hF hO hD i)

/-- Genuine A_i* (1+B)^{-1}; the constant input has not been discarded. -/
def normalizedRaising (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
  LinearMap.mkContinuous
    ({ toFun := normalizedRaisingOutput hF hO hD i
       map_add' := normalizedRaisingOutput_add hF hO hD i
       map_smul' := normalizedRaisingOutput_smul hF hO hD i } : SphereL2 →ₗ[ℝ] SphereL2)
    2 (norm_normalizedRaisingOutput_le hF hO hD i)

lemma normalizedDerivative_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u w : SphereL2) (hw : (u,w) ∈ sphereBesselGraph hO hD 1) :
    (u,normalizedDerivative hF hO hD i w) ∈ sphereDerivativeGraph hF hO hD i := by
  rw [← inverseDegreeMultiplier_of_besselGraph hO hD u w hw]
  exact normalizedDerivativeOutput_graph hF hO hD i w

lemma normalizedRaising_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u w : SphereL2) (hw : (u,w) ∈ sphereBesselGraph hO hD 1) :
    (u,normalizedRaising hF hO hD i w) ∈ sphereRaisingGraph hF hO hD i := by
  rw [← inverseDegreeMultiplier_of_besselGraph hO hD u w hw]
  exact normalizedRaisingOutput_graph hF hO hD i w

lemma norm_normalizedDerivative_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3) :
    ‖normalizedDerivative hF hO hD i‖ ≤ 2 :=
  (normalizedDerivative hF hO hD i).opNorm_le_bound (by norm_num)
    (norm_normalizedDerivativeOutput_le hF hO hD i)

lemma norm_normalizedRaising_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3) :
    ‖normalizedRaising hF hO hD i‖ ≤ 2 :=
  (normalizedRaising hF hO hD i).opNorm_le_bound (by norm_num)
    (norm_normalizedRaisingOutput_le hF hO hD i)

end OAI.AnisotropicCalderon.BoundedAngularShift
