import Calderon.SpectralWeightComparison
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.BoundedSpectralMultiplier
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SpectralWeightedGraph SpectralWeightComparison

def boundedSpectralOutput (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ k, |w k| ≤ C) (u : SphereL2) : SphereL2 :=
  (exists_spectralGraph_of_weight_le hO hD w (fun _ => 1) C hC
    (by simpa only [abs_one,mul_one] using hw) u u
    (by intro k; exact (one_smul ℝ _).symm)).choose

lemma boundedSpectralOutput_mem (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ k, |w k| ≤ C) (u : SphereL2) :
    (u,boundedSpectralOutput hO hD w C hC hw u) ∈ spectralGraph hO hD w :=
  (exists_spectralGraph_of_weight_le hO hD w (fun _ => 1) C hC
    (by simpa only [abs_one,mul_one] using hw) u u
    (by intro k; exact (one_smul ℝ _).symm)).choose_spec

lemma boundedSpectralOutput_add (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ k, |w k| ≤ C) (u v : SphereL2) :
    boundedSpectralOutput hO hD w C hC hw (u+v) =
      boundedSpectralOutput hO hD w C hC hw u + boundedSpectralOutput hO hD w C hC hw v := by
  apply spectralGraph_output_unique hO hD w (u+v)
  · exact boundedSpectralOutput_mem hO hD w C hC hw (u+v)
  · intro k
    change sphereHarmonicCoordinate hO hD k
        (boundedSpectralOutput hO hD w C hC hw u + boundedSpectralOutput hO hD w C hC hw v) =
      w k • sphereHarmonicCoordinate hO hD k (u+v)
    rw [map_add,map_add,boundedSpectralOutput_mem hO hD w C hC hw u k,
      boundedSpectralOutput_mem hO hD w C hC hw v k,smul_add]

lemma boundedSpectralOutput_smul (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ k, |w k| ≤ C) (c : ℝ) (u : SphereL2) :
    boundedSpectralOutput hO hD w C hC hw (c • u) =
      c • boundedSpectralOutput hO hD w C hC hw u := by
  apply spectralGraph_output_unique hO hD w (c • u)
  · exact boundedSpectralOutput_mem hO hD w C hC hw (c • u)
  · intro k
    change sphereHarmonicCoordinate hO hD k (c • boundedSpectralOutput hO hD w C hC hw u) =
      w k • sphereHarmonicCoordinate hO hD k (c • u)
    rw [map_smul,map_smul,boundedSpectralOutput_mem hO hD w C hC hw u k,smul_comm]

lemma norm_boundedSpectralOutput_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, |w k| ≤ C) (u : SphereL2) :
    ‖boundedSpectralOutput hO hD w C hC hw u‖ ≤ C * ‖u‖ :=
  norm_spectralGraph_output_le hO hD w (fun _ => 1) C hC
    (by simpa only [abs_one,mul_one] using hw) u _ u
    (boundedSpectralOutput_mem hO hD w C hC hw u)
    (by intro k; exact (one_smul ℝ _).symm)

def boundedSpectralMultiplier (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ k, |w k| ≤ C) : SphereL2 →L[ℝ] SphereL2 :=
  LinearMap.mkContinuous
    ({ toFun := boundedSpectralOutput hO hD w C hC hw
       map_add' := boundedSpectralOutput_add hO hD w C hC hw
       map_smul' := boundedSpectralOutput_smul hO hD w C hC hw } : SphereL2 →ₗ[ℝ] SphereL2)
    C (norm_boundedSpectralOutput_le hO hD w C hC hw)

lemma boundedSpectralMultiplier_mem (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, |w k| ≤ C) (u : SphereL2) :
    (u,boundedSpectralMultiplier hO hD w C hC hw u) ∈ spectralGraph hO hD w :=
  boundedSpectralOutput_mem hO hD w C hC hw u

lemma norm_boundedSpectralMultiplier_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, |w k| ≤ C) : ‖boundedSpectralMultiplier hO hD w C hC hw‖ ≤ C :=
  (boundedSpectralMultiplier hO hD w C hC hw).opNorm_le_bound hC
    (norm_boundedSpectralOutput_le hO hD w C hC hw)

def casimirBesselRatio (s : ℝ) (k : ℕ) : ℝ := besselWeight s k / casimirWeight k

lemma abs_casimirBesselRatio_le_two (s : ℝ) (hs : s ≤ 2) (k : ℕ) :
    |casimirBesselRatio s k| ≤ 2 := by
  rw [casimirBesselRatio,abs_div,abs_of_nonneg (casimirWeight_pos k).le]
  exact (div_le_iff₀ (casimirWeight_pos k)).mpr
    (abs_besselWeight_le_two_casimirWeight s hs k)

def casimirBesselMultiplier (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : s ≤ 2) : SphereL2 →L[ℝ] SphereL2 :=
  boundedSpectralMultiplier hO hD (casimirBesselRatio s) 2 (by norm_num)
    (abs_casimirBesselRatio_le_two s hs)

theorem casimirBesselMultiplier_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2) (u v : SphereL2)
    (hv : (u,v) ∈ spectralGraph hO hD casimirWeight) :
    (u,casimirBesselMultiplier hO hD s hs v) ∈ sphereBesselGraph hO hD s := by
  have hb := boundedSpectralMultiplier_mem hO hD (casimirBesselRatio s) 2
    (by norm_num) (abs_casimirBesselRatio_le_two s hs) v
  intro k
  change sphereHarmonicCoordinate hO hD k
      (boundedSpectralMultiplier hO hD (casimirBesselRatio s) 2 (by norm_num)
        (abs_casimirBesselRatio_le_two s hs) v) =
    besselWeight s k • sphereHarmonicCoordinate hO hD k u
  rw [hb k,hv k,smul_smul]
  change (besselWeight s k / casimirWeight k * casimirWeight k) •
    sphereHarmonicCoordinate hO hD k u = _
  rw [div_mul_cancel₀ _ (casimirWeight_pos k).ne']

lemma norm_casimirBesselMultiplier_apply_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2) (v : SphereL2) :
    ‖casimirBesselMultiplier hO hD s hs v‖ ≤ 2 * ‖v‖ :=
  norm_boundedSpectralOutput_le hO hD (casimirBesselRatio s) 2 (by norm_num)
    (abs_casimirBesselRatio_le_two s hs) v

lemma contDiff_casimirBesselMultiplier (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2) (V : R3 → SphereL2)
    (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (fun x => casimirBesselMultiplier hO hD s hs (V x)) :=
  (casimirBesselMultiplier hO hD s hs).contDiff.comp hV

lemma fderiv_casimirBesselMultiplier (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2) (V : R3 → SphereL2) (x : R3)
    (hV : DifferentiableAt ℝ V x) :
    fderiv ℝ (fun y => casimirBesselMultiplier hO hD s hs (V y)) x =
      (casimirBesselMultiplier hO hD s hs).comp (fderiv ℝ V x) :=
  ((casimirBesselMultiplier hO hD s hs).hasFDerivAt.comp x hV.hasFDerivAt).fderiv

lemma hasCompactSupport_casimirBesselMultiplier (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2) (V : R3 → SphereL2)
    (hV : HasCompactSupport V) :
    HasCompactSupport (fun x => casimirBesselMultiplier hO hD s hs (V x)) :=
  hV.comp_left (map_zero (casimirBesselMultiplier hO hD s hs))

end OAI.AnisotropicCalderon.BoundedSpectralMultiplier
