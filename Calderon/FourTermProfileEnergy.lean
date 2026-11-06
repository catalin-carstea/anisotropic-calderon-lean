import Calderon.WeightedSpectralEnergy

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.FourTermProfileEnergy
open SphereHarmonic SpectralCoreRegularity WeightedBaseSpectral WeightedSpectralEnergy
  ReferenceDensityBounds

/-- The precise manuscript four terms, on constructed fields. -/
def fourTermEnergyDensity (beta : R3 → ℝ) (H : Fin 3 → R3 → SphereL2)
    (U1 : R3 → SphereL2) (Hhalf : Fin 3 → R3 → SphereL2)
    (Uthree : R3 → SphereL2) (x : R3) : ℝ :=
  (∑ i : Fin 3, ‖H i x‖^2) + beta x^2 * ‖U1 x‖^2 +
    (beta x)⁻¹ * (∑ i : Fin 3, ‖Hhalf i x‖^2) + beta x * ‖Uthree x‖^2

def fourTermCutDensity (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (n : ℕ) (beta : R3 → ℝ) (H : Fin 3 → R3 → SphereL2)
    (U1 : R3 → SphereL2) (Hhalf : Fin 3 → R3 → SphereL2)
    (Uthree : R3 → SphereL2) : R3 → ℝ :=
  fourTermEnergyDensity beta
    (fun i x => sphereShiftPartialSum hO hD 1 n (H i x))
    (fun x => sphereShiftPartialSum hO hD 1 n (U1 x))
    (fun i x => sphereShiftPartialSum hO hD 1 n (Hhalf i x))
    (fun x => sphereShiftPartialSum hO hD 1 n (Uthree x))

lemma continuous_fourTermEnergyDensity (beta : R3 → ℝ) (hb : Continuous beta)
    (hbi : Continuous (fun x => (beta x)⁻¹))
    (H : Fin 3 → R3 → SphereL2) (hH : ∀ i, Continuous (H i))
    (U1 : R3 → SphereL2) (h1 : Continuous U1)
    (Hhalf : Fin 3 → R3 → SphereL2) (hh : ∀ i, Continuous (Hhalf i))
    (Uthree : R3 → SphereL2) (h3 : Continuous Uthree) :
    Continuous (fourTermEnergyDensity beta H U1 Hhalf Uthree) :=
  ((((continuous_finsetSum Finset.univ (fun i _ => (hH i).norm.pow 2)).add
    ((hb.pow 2).mul (h1.norm.pow 2))).add
    (hbi.mul (continuous_finsetSum Finset.univ (fun i _ => (hh i).norm.pow 2)))).add
    (hb.mul (h3.norm.pow 2)))

lemma fourTermEnergyDensity_nonneg (beta : R3 → ℝ)
    (H : Fin 3 → R3 → SphereL2) (U1 : R3 → SphereL2)
    (Hhalf : Fin 3 → R3 → SphereL2) (Uthree : R3 → SphereL2)
    (x : R3) (hb : 0 ≤ beta x) : 0 ≤ fourTermEnergyDensity beta H U1 Hhalf Uthree x := by
  unfold fourTermEnergyDensity
  positivity

lemma fourTermCutDensity_le (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (n : ℕ) (beta : R3 → ℝ) (H : Fin 3 → R3 → SphereL2) (U1 : R3 → SphereL2)
    (Hhalf : Fin 3 → R3 → SphereL2) (Uthree : R3 → SphereL2)
    (x : R3) (hb : 0 ≤ beta x) :
    fourTermCutDensity hO hD n beta H U1 Hhalf Uthree x ≤
      fourTermEnergyDensity beta H U1 Hhalf Uthree x := by
  have hn (u : SphereL2) : ‖sphereShiftPartialSum hO hD 1 n u‖^2 ≤ ‖u‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (norm_sphereShiftPartialSum_le hO hD 1 n u)
  exact add_le_add
    (add_le_add
      (add_le_add (Finset.sum_le_sum (fun i _ => hn (H i x)))
        (mul_le_mul_of_nonneg_left (hn (U1 x)) (sq_nonneg _)))
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hn (Hhalf i x)))
        (inv_nonneg.mpr hb)))
    (mul_le_mul_of_nonneg_left (hn (Uthree x)) hb)

lemma fourTermEnergyDensity_eq_zero (beta : R3 → ℝ)
    (H : Fin 3 → R3 → SphereL2) (U1 : R3 → SphereL2)
    (Hhalf : Fin 3 → R3 → SphereL2) (Uthree : R3 → SphereL2) (x : R3)
    (hH : ∀ i, H i x=0) (h1 : U1 x=0) (hh : ∀ i, Hhalf i x=0) (h3 : Uthree x=0) :
    fourTermEnergyDensity beta H U1 Hhalf Uthree x=0 := by
  simp only [fourTermEnergyDensity,hH,h1,hh,h3,norm_zero,zero_pow (by omega : 2≠0),
    Finset.sum_const_zero,mul_zero,add_zero]

lemma fourTermCutDensity_eq_zero (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (n : ℕ) (beta : R3 → ℝ) (H : Fin 3 → R3 → SphereL2) (U1 : R3 → SphereL2)
    (Hhalf : Fin 3 → R3 → SphereL2) (Uthree : R3 → SphereL2) (x : R3)
    (hH : ∀ i, H i x=0) (h1 : U1 x=0) (hh : ∀ i, Hhalf i x=0) (h3 : Uthree x=0) :
    fourTermCutDensity hO hD n beta H U1 Hhalf Uthree x=0 := by
  unfold fourTermCutDensity
  apply fourTermEnergyDensity_eq_zero
  all_goals simp [sphereShiftPartialSum,hH,h1,hh,h3]

lemma tendsto_fourTermCutDensity (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta : R3 → ℝ) (H : Fin 3 → R3 → SphereL2) (U1 : R3 → SphereL2)
    (Hhalf : Fin 3 → R3 → SphereL2) (Uthree : R3 → SphereL2) (x : R3)
    (hzH : ∀ i, sphereHarmonicCoordinate hO hD 0 (H i x)=0)
    (hz1 : sphereHarmonicCoordinate hO hD 0 (U1 x)=0)
    (hzh : ∀ i, sphereHarmonicCoordinate hO hD 0 (Hhalf i x)=0)
    (hz3 : sphereHarmonicCoordinate hO hD 0 (Uthree x)=0) :
    Tendsto (fun n : ℕ => fourTermCutDensity hO hD n beta H U1 Hhalf Uthree x)
      atTop (𝓝 (fourTermEnergyDensity beta H U1 Hhalf Uthree x)) := by
  have ht (u : SphereL2) (hu : sphereHarmonicCoordinate hO hD 0 u=0) :
      Tendsto (fun n : ℕ => ‖sphereShiftPartialSum hO hD 1 n u‖^2) atTop (𝓝 (‖u‖^2)) :=
    (tendsto_sphereShiftPartialSum hO hD 1 u (by
      intro k hk
      have hk0 : k=0 := by omega
      subst k
      exact hu)).norm.pow 2
  exact (((tendsto_finset_sum Finset.univ (fun i _ => ht (H i x) (hzH i))).add
    ((ht (U1 x) hz1).const_mul (beta x^2))).add
    ((tendsto_finset_sum Finset.univ (fun i _ => ht (Hhalf i x) (hzh i))).const_mul (beta x)⁻¹)).add
      ((ht (Uthree x) hz3).const_mul (beta x))

/-- Actual compact fields imply the complete four-term limit; no convergence premise. -/
theorem tendsto_integral_fourTermCutDensity
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta : R3 → ℝ) (hb : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (H : Fin 3 → R3 → SphereL2) (hH : ∀ i, Continuous (H i))
    (U1 : R3 → SphereL2) (h1 : Continuous U1)
    (Hhalf : Fin 3 → R3 → SphereL2) (hh : ∀ i, Continuous (Hhalf i))
    (Uthree : R3 → SphereL2) (h3 : Continuous Uthree)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, (∀ i, H i x=0) ∧ U1 x=0 ∧ (∀ i, Hhalf i x=0) ∧ Uthree x=0)
    (hz0 : ∀ x, (∀ i, sphereHarmonicCoordinate hO hD 0 (H i x)=0) ∧
      sphereHarmonicCoordinate hO hD 0 (U1 x)=0 ∧
      (∀ i, sphereHarmonicCoordinate hO hD 0 (Hhalf i x)=0) ∧
      sphereHarmonicCoordinate hO hD 0 (Uthree x)=0) :
    Tendsto (fun n : ℕ => ∫ x, referenceDensityFamily g L (lam,x) *
      fourTermCutDensity hO hD n beta H U1 Hhalf Uthree x) atTop
      (𝓝 (∫ x, referenceDensityFamily g L (lam,x) * fourTermEnergyDensity beta H U1 Hhalf Uthree x)) := by
  have hbi : Continuous (fun x => (beta x)⁻¹) := hb.inv₀ (fun x => (hpos x).ne')
  have hE := continuous_fourTermEnergyDensity beta hb hbi H hH U1 h1 Hhalf hh Uthree h3
  have hEc : HasCompactSupport (fourTermEnergyDensity beta H U1 Hhalf Uthree) :=
    HasCompactSupport.intro hK (fun x hx =>
      fourTermEnergyDensity_eq_zero beta H U1 Hhalf Uthree x (hz x hx).1
        (hz x hx).2.1 (hz x hx).2.2.1 (hz x hx).2.2.2)
  have hI : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      fourTermEnergyDensity beta H U1 Hhalf Uthree x) :=
    ((continuous_referenceBaseDensity g hg L lam).mul hE).integrable_of_hasCompactSupport hEc.mul_left
  apply tendsto_integral_of_dominated_convergence
    (fun x => referenceDensityFamily g L (lam,x) * fourTermEnergyDensity beta H U1 Hhalf Uthree x)
  · intro n
    exact ((continuous_referenceBaseDensity g hg L lam).mul
      (continuous_fourTermEnergyDensity beta hb hbi _
        (fun i => continuous_sphereShiftPartialSum hO hD 1 n (H i) (hH i)) _
        (continuous_sphereShiftPartialSum hO hD 1 n U1 h1) _
        (fun i => continuous_sphereShiftPartialSum hO hD 1 n (Hhalf i) (hh i)) _
        (continuous_sphereShiftPartialSum hO hD 1 n Uthree h3))).aestronglyMeasurable
  · exact hI
  · intro n
    apply Filter.Eventually.of_forall
    intro x
    have hn : 0 ≤ fourTermCutDensity hO hD n beta H U1 Hhalf Uthree x :=
      fourTermEnergyDensity_nonneg beta _ _ _ _ x (hpos x).le
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (referenceDensityFamily_pos g hg L (lam,x)).le hn)]
    exact mul_le_mul_of_nonneg_left (fourTermCutDensity_le hO hD n beta H U1 Hhalf Uthree x (hpos x).le)
      (referenceDensityFamily_pos g hg L (lam,x)).le
  · apply Filter.Eventually.of_forall
    intro x
    exact (tendsto_fourTermCutDensity hO hD beta H U1 Hhalf Uthree x
      (hz0 x).1 (hz0 x).2.1 (hz0 x).2.2.1 (hz0 x).2.2.2).const_mul
        (referenceDensityFamily g L (lam,x))

end OAI.AnisotropicCalderon.FourTermProfileEnergy
