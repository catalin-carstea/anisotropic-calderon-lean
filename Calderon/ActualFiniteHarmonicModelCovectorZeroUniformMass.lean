import Calderon.ActualFiniteHarmonicModelReferenceCovectorZeroExpansion
import Calderon.ActualFiniteHarmonicModelConnectionDerivativeMassBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  AmbientReferenceRaising ConformalDepth MovingFrameConnection ReferenceWeightedApproximation

theorem exists_nativeReferenceCovectorZeroRawMass_uniform_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      let beta := actualReferenceBeta g L lam δ R p x
      1 ≤ beta → ∀ a b : Fin 3,
      nativeReferenceCovectorZeroRawMass g L lam δ R p a b x ≤ C*beta^2 := by
  obtain ⟨A,hA,hconn⟩ := exists_nativeReferenceConnection_uniform_expansion_masses hO hD g hg L K hK
  obtain ⟨J,hJ,hprof⟩ := exists_nativeReferenceProfile_uniform_first_second_frame_bounds g hg L hL K hK
  let T := 1+A+J
  have hT : 1 ≤ T := by dsimp only [T]; linarith
  have hT0 : 0 ≤ T := by linarith
  have hAT : A ≤ T := by dsimp only [T]; linarith
  have hJT : J ≤ T := by dsimp only [T]; linarith
  refine ⟨7*T^2,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb a b
  have hb0 : 0 ≤ beta := by linarith
  have hb2 : beta ≤ beta^2 := by nlinarith
  have hb21 : 1 ≤ beta^2 := by nlinarith
  let q (c : Fin 3) := referenceFrameDerivative g L lam c (fun y => Real.log (referenceRadius δ R p L y))
  let M (c : Fin 3) := nativeReferenceWeightedZeroRawMass g L lam δ R p c x
  have hM0 (c : Fin 3) : 0 ≤ M c := by
    dsimp only [M,nativeReferenceWeightedZeroRawMass,nativeReferenceConnectionCoefficientMass]
    positivity
  have hq (c : Fin 3) : |q c x| ≤ J*beta := (hprof lam hlam δ hδ hδ1 R hR p hp x hx hb c b).1
  have hM (c : Fin 3) : M c ≤ T*beta := by
    have hc := (hconn lam hlam x hx).1 c
    have ha : A ≤ A*beta := le_mul_of_one_le_right hA.le hb
    have hp := hq c
    dsimp only [M,nativeReferenceWeightedZeroRawMass,T]
    change |referenceFrameDerivative g L lam c (fun y => Real.log (referenceRadius δ R p L y)) x| ≤ J*beta at hp
    nlinarith
  have hdA : nativeReferenceConnectionDerivativeMass g L lam a b x ≤ T*beta^2 := by
    exact ((hconn lam hlam x hx).2.1 a b).trans (hAT.trans (le_mul_of_one_le_right hT0 hb21))
  have hdP : |referenceFrameDerivative g L lam a (q b) x| ≤ T*beta^2 :=
    ((hprof lam hlam δ hδ hδ1 R hR p hp x hx hb a b).2).trans
      (mul_le_mul_of_nonneg_right hJT (sq_nonneg beta))
  have hlinear (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ A) (c : Fin 3) : v*M c ≤ T^2*beta^2 := by
    have hvT : v ≤ T*beta := hv.trans (hAT.trans (le_mul_of_one_le_right hT0 hb))
    calc
      _ ≤ (T*beta)*(T*beta) := mul_le_mul hvT (hM c) (hM0 c) (mul_nonneg hT0 hb0)
      _ = _ := by ring
  have hprod : nativeReferenceConnectionCoefficientMass g L lam a x*M b ≤ T^2*beta^2 := by
    apply hlinear
    · unfold nativeReferenceConnectionCoefficientMass; positivity
    · exact (hconn lam hlam x hx).1 a
  have hgamma (c : Fin 3) : |referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) a) c b| *M c ≤ T^2*beta^2 :=
    hlinear _ (abs_nonneg _) ((hconn lam hlam x hx).2.2 a c b) c
  have hs := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Fin 3))) => hgamma c)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
  have hlast : |q a x| *M b ≤ T^2*beta^2 := by
    calc
      _ ≤ (T*beta)*(T*beta) := mul_le_mul
        ((hq a).trans (mul_le_mul_of_nonneg_right hJT hb0)) (hM b) (hM0 b) (mul_nonneg hT0 hb0)
      _ = _ := by ring
  have hTT : T*beta^2 ≤ T^2*beta^2 :=
    mul_le_mul_of_nonneg_right (by nlinarith : T ≤ T^2) (sq_nonneg beta)
  change nativeReferenceConnectionDerivativeMass g L lam a b x+
    |referenceFrameDerivative g L lam a (q b) x|+
    nativeReferenceConnectionCoefficientMass g L lam a x*M b+
    (∑ c : Fin 3, |referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) a) c b| *M c)+|q a x| *M b ≤ _
  nlinarith

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
