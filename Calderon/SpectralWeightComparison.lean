import Calderon.SpectralWeightedGraph

set_option autoImplicit false
noncomputable section
open scoped Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SpectralWeightComparison
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph

def casimirWeight (k : ℕ) : ℝ := 1 + (k : ℝ) * ((k : ℝ) + 1)

lemma casimirWeight_pos (k : ℕ) : 0 < casimirWeight k := by
  unfold casimirWeight
  positivity

theorem abs_besselWeight_le_two_casimirWeight (s : ℝ) (hs : s ≤ 2) (k : ℕ) :
    |besselWeight s k| ≤ 2 * casimirWeight k := by
  rw [abs_of_nonneg (besselWeight_pos s k).le]
  have hr : besselWeight s k ≤ (1 + (k : ℝ)) ^ 2 := by
    simpa only [besselWeight,Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (Nat.cast_nonneg k)) hs
  unfold casimirWeight
  nlinarith [sq_nonneg (k : ℝ)]

lemma norm_spectralGraph_coordinate_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w z : ℕ → ℝ) (C : ℝ) (hw : ∀ k, |w k| ≤ C * |z k|)
    (u b v : SphereL2) (hb : (u,b) ∈ spectralGraph hO hD w)
    (hv : (u,v) ∈ spectralGraph hO hD z) (k : ℕ) :
    ‖sphereHarmonicCoordinate hO hD k b‖ ≤ C * ‖sphereHarmonicCoordinate hO hD k v‖ := by
  rw [hb k,hv k]
  simp only [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ (C * |z k|) * ‖sphereHarmonicCoordinate hO hD k u‖ :=
      mul_le_mul_of_nonneg_right (hw k) (norm_nonneg _)
    _ = _ := by ring

theorem exists_spectralGraph_of_weight_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w z : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ k, |w k| ≤ C * |z k|)
    (u v : SphereL2) (hv : (u,v) ∈ spectralGraph hO hD z) :
    ∃ b : SphereL2, (u,b) ∈ spectralGraph hO hD w := by
  have ht (k : ℕ) : ‖spectralCoordinateSequence hO hD w u k‖ ≤
      C * ‖sphereHarmonicCoordinate hO hD k v‖ := by
    rw [spectralCoordinateSequence,hv k]
    simp only [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (C * |z k|) * ‖sphereHarmonicCoordinate hO hD k u‖ :=
        mul_le_mul_of_nonneg_right (hw k) (norm_nonneg _)
      _ = _ := by ring
  have hm : Memℓp (spectralCoordinateSequence hO hD w u) 2 :=
    (lp.memℓp (C • sphereHarmonicDecomposition hO hD v)).mono' (fun k => by
      simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg hC,sphereHarmonicCoordinate_apply] using ht k)
  exact (exists_spectralGraph_iff_summable hO hD w u).mpr
    ((memLp_spectralCoordinateSequence_iff hO hD w u).mp hm)

theorem norm_spectralGraph_output_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w z : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ k, |w k| ≤ C * |z k|)
    (u b v : SphereL2) (hb : (u,b) ∈ spectralGraph hO hD w)
    (hv : (u,v) ∈ spectralGraph hO hD z) : ‖b‖ ≤ C * ‖v‖ := by
  have hp := lp.norm_mono (p := 2) (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (x := sphereHarmonicDecomposition hO hD b)
    (y := C • sphereHarmonicDecomposition hO hD v) (fun k => by
      simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg hC,sphereHarmonicCoordinate_apply] using
        norm_spectralGraph_coordinate_le hO hD w z C hw u b v hb hv k)
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC,
    LinearIsometryEquiv.norm_map] using hp

theorem norm_spectralGraph_tail_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w z : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ k, |w k| ≤ C * |z k|)
    (u b v : SphereL2) (hb : (u,b) ∈ spectralGraph hO hD w)
    (hv : (u,v) ∈ spectralGraph hO hD z) (n : ℕ) :
    ‖b - sphereHarmonicPartialSum hO hD n b‖ ≤
      C * ‖v - sphereHarmonicPartialSum hO hD n v‖ := by
  have hbt : (u - sphereHarmonicPartialSum hO hD n u,
      b - sphereHarmonicPartialSum hO hD n b) ∈ spectralGraph hO hD w := by
    intro k
    change sphereHarmonicCoordinate hO hD k (b - sphereHarmonicPartialSum hO hD n b) =
      w k • sphereHarmonicCoordinate hO hD k (u - sphereHarmonicPartialSum hO hD n u)
    have hs := spectralGraph_partialSum hO hD w (u,b) hb n
    rw [map_sub,map_sub,hb k,hs k,smul_sub]
  have hvt : (u - sphereHarmonicPartialSum hO hD n u,
      v - sphereHarmonicPartialSum hO hD n v) ∈ spectralGraph hO hD z := by
    intro k
    change sphereHarmonicCoordinate hO hD k (v - sphereHarmonicPartialSum hO hD n v) =
      z k • sphereHarmonicCoordinate hO hD k (u - sphereHarmonicPartialSum hO hD n u)
    have hs := spectralGraph_partialSum hO hD z (u,v) hv n
    rw [map_sub,map_sub,hv k,hs k,smul_sub]
  exact norm_spectralGraph_output_le hO hD w z C hC hw _ _ _ hbt hvt

theorem exists_sphereBesselGraph_of_casimirGraph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : s ≤ 2) (u v : SphereL2)
    (hv : (u,v) ∈ spectralGraph hO hD casimirWeight) :
    ∃ b : SphereL2, (u,b) ∈ sphereBesselGraph hO hD s := by
  apply exists_spectralGraph_of_weight_le hO hD (besselWeight s) casimirWeight 2
    (by norm_num) ?_ u v hv
  intro k
  rw [abs_of_nonneg (casimirWeight_pos k).le]
  exact abs_besselWeight_le_two_casimirWeight s hs k

theorem norm_sphereBesselGraph_output_le_casimirGraph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : s ≤ 2) (u b v : SphereL2)
    (hb : (u,b) ∈ sphereBesselGraph hO hD s)
    (hv : (u,v) ∈ spectralGraph hO hD casimirWeight) : ‖b‖ ≤ 2 * ‖v‖ := by
  apply norm_spectralGraph_output_le hO hD (besselWeight s) casimirWeight 2
    (by norm_num) ?_ u b v hb hv
  intro k
  rw [abs_of_nonneg (casimirWeight_pos k).le]
  exact abs_besselWeight_le_two_casimirWeight s hs k

theorem norm_sphereBesselGraph_tail_le_casimirGraph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : s ≤ 2) (u b v : SphereL2)
    (hb : (u,b) ∈ sphereBesselGraph hO hD s)
    (hv : (u,v) ∈ spectralGraph hO hD casimirWeight) (n : ℕ) :
    ‖b - sphereHarmonicPartialSum hO hD n b‖ ≤
      2 * ‖v - sphereHarmonicPartialSum hO hD n v‖ := by
  apply norm_spectralGraph_tail_le hO hD (besselWeight s) casimirWeight 2
    (by norm_num) ?_ u b v hb hv n
  intro k
  rw [abs_of_nonneg (casimirWeight_pos k).le]
  exact abs_besselWeight_le_two_casimirWeight s hs k

end OAI.AnisotropicCalderon.SpectralWeightComparison
