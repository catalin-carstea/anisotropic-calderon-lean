import Calderon.SphereAngularRaisingPolynomial
import Calderon.ActualNativeMovingAdjointFiniteJ
import Calderon.SphereSobolevSingleRotationAngleDerivative

/-! Exact canonical raising graph, with no output premise. -/
set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial HarmonicCoordinateCompatibility SphereDerivativeAdjoint
  HarmonicDerivativeOperator SmoothSphereRotationProjection

lemma sum_harmonicSphereRotation_radialDriftBlock
    (hF : SphereFischerInner) (m : ℕ) (u : harmonicSphereSubspace (m+1))
    (i : Fin 3) :
    (∑ j : Fin 3, harmonicSphereRotation m j i
      (radialDriftBlockL hF (EuclideanSpace.single j 1) m u)) =
        (m : ℝ) • radialDriftBlockL hF (EuclideanSpace.single i 1) m u := by
  rcases harmonicPolynomialSphereMap_surjective (m+1) u with ⟨p,rfl⟩
  let c : ℝ := -(2*((m+1 : ℕ) : ℝ)+1)⁻¹
  have hB (j : Fin 3) :
      radialDriftBlockL hF (EuclideanSpace.single j 1) m
        (harmonicPolynomialSphereMap (m+1) p) =
      c • harmonicPolynomialDerivativeMap m j p := by
    have hSum : (∑ l : Fin 3, ((EuclideanSpace.single j (1 : ℝ)) l) •
        harmonicDerivative hF m l (harmonicPolynomialSphereMap (m+1) p)) =
          harmonicDerivative hF m j (harmonicPolynomialSphereMap (m+1) p) := by
      classical
      rw [Finset.sum_eq_single j]
      · simp (config := { instances := true }) only
          [EuclideanSpace.single_apply,ite_true,if_pos rfl,one_smul]
      · intro l hl hlj
        simp (config := { instances := true }) only
          [EuclideanSpace.single_apply,if_neg hlj,zero_smul]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    calc
      _ = c • (∑ l : Fin 3, ((EuclideanSpace.single j (1 : ℝ)) l) •
          harmonicDerivative hF m l (harmonicPolynomialSphereMap (m+1) p)) := by
        simp (config := { instances := true }) only [radialDriftBlockL,c,
          ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply]
      _ = c • harmonicDerivative hF m j (harmonicPolynomialSphereMap (m+1) p) :=
        congrArg (fun v : harmonicSphereSubspace m => c • v) hSum
      _ = _ := congrArg (fun v : harmonicSphereSubspace m => c • v)
        (harmonicDerivative_apply_image hF m j p)
  have hRot (j : Fin 3) :
      (harmonicSphereRotation m j i (harmonicPolynomialDerivativeMap m j p) : SphereL2) =
        polynomialSphereL2 (polynomialRotation j i (pderiv j (p : MvPolynomial (Fin 3) ℝ))) := by
    change (harmonicSphereRotation m j i (harmonicPolynomialSphereMap m
      ⟨pderiv j (p : MvPolynomial (Fin 3) ℝ),
        pderiv_harmonicHomogeneous_succ m j p p.property⟩) : SphereL2) = _
    exact congrArg Subtype.val (harmonicSphereRotation_apply_image m j i _)
  have hIndex : ((m+1 : ℕ) : ℝ)-1 = (m : ℝ) := by push_cast; ring
  have hPoly : (∑ j : Fin 3, polynomialSphereL2
      (polynomialRotation j i (pderiv j (p : MvPolynomial (Fin 3) ℝ)))) =
        (m : ℝ) • polynomialSphereL2 (pderiv i (p : MvPolynomial (Fin 3) ℝ)) := by
    have h := congrArg polynomialSphereL2
      (sum_polynomialRotation_pderiv_harmonic (m+1) p p.property i)
    simpa only [map_sum,hIndex,← smul_eq_C_mul,map_smul] using h
  apply Subtype.ext
  simp only [hB,map_smul,Submodule.coe_sum,Submodule.coe_smul]
  simp_rw [hRot]
  rw [← Finset.smul_sum,hPoly]
  change c • ((m : ℝ) • polynomialSphereL2 (pderiv i (p : MvPolynomial (Fin 3) ℝ))) =
    (m : ℝ) • (c • polynomialSphereL2 (pderiv i (p : MvPolynomial (Fin 3) ℝ)))
  exact smul_comm c (m : ℝ) _

lemma neg_sum_harmonicSphereRotation_radialDriftAdjointBlock_add_degree
    (hF : SphereFischerInner) (k : ℕ) (u : harmonicSphereSubspace k)
    (i : Fin 3) :
    -(∑ j : Fin 3, harmonicSphereRotation (k+1) j i
      (radialDriftAdjointBlockL hF (EuclideanSpace.single j 1) k u)) +
        ((k+1 : ℕ) : ℝ) • radialDriftAdjointBlockL hF (EuclideanSpace.single i 1) k u =
      -harmonicDerivativeAdjoint hF k i u := by
  rcases harmonicPolynomialSphereMap_surjective k u with ⟨p,rfl⟩
  let c : ℝ := -(2*((k+1 : ℕ) : ℝ)+1)⁻¹
  let V (j : Fin 3) := harmonicDerivativeAdjoint hF k j (harmonicPolynomialSphereMap k p)
  have hB (j : Fin 3) : radialDriftAdjointBlockL hF (EuclideanSpace.single j 1) k
      (harmonicPolynomialSphereMap k p) = c • V j := by
    have hSum : (∑ l : Fin 3, ((EuclideanSpace.single j (1 : ℝ)) l) •
        harmonicDerivativeAdjoint hF k l (harmonicPolynomialSphereMap k p)) = V j := by
      classical
      rw [Finset.sum_eq_single j]
      · simp (config := { instances := true }) only
          [EuclideanSpace.single_apply,ite_true,if_pos rfl,one_smul,V]
      · intro l hl hlj
        simp (config := { instances := true }) only
          [EuclideanSpace.single_apply,if_neg hlj,zero_smul]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    have hBlock := congrArg (fun T : harmonicSphereSubspace k →L[ℝ]
      harmonicSphereSubspace (k+1) => T (harmonicPolynomialSphereMap k p))
        (radialDriftAdjointBlockL_eq hF (EuclideanSpace.single j 1) k)
    simp (config := { instances := true }) only
      [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply] at hBlock
    exact hBlock.trans (congrArg (fun v : harmonicSphereSubspace (k+1) => c • v) hSum)
  have hPoly : (∑ j : Fin 3, polynomialRotation j i
      (sphereDerivativeAdjoint k j (p : MvPolynomial (Fin 3) ℝ))) =
        -C ((k : ℝ)+2) * sphereDerivativeAdjoint k i p := by
    have hFactor (j : Fin 3) : polynomialRotation j i (sphereDerivativeAdjoint k j p) =
        C (2*(k : ℝ)+3) * polynomialRotation j i (coordinateHarmonicRaising k j p) := by
      simp only [sphereDerivativeAdjoint,polynomialRotation,pderiv_C_mul]
      ring
    simp_rw [hFactor]
    rw [← Finset.mul_sum,sum_polynomialRotation_coordinateHarmonicRaising k p p.property i]
    unfold sphereDerivativeAdjoint
    ring
  have hRot : (∑ j : Fin 3, harmonicSphereRotation (k+1) j i (V j)) =
      -((k : ℝ)+2) • V i := by
    apply Subtype.ext
    have hTerm (j : Fin 3) :
        (harmonicSphereRotation (k+1) j i (V j) : SphereL2) =
          polynomialSphereL2 (polynomialRotation j i (sphereDerivativeAdjoint k j p)) := by
      dsimp [V]
      rw [harmonicDerivativeAdjoint_apply_image]
      change (harmonicSphereRotation (k+1) j i (harmonicPolynomialSphereMap (k+1)
        ⟨sphereDerivativeAdjoint k j p,
          sphereDerivativeAdjoint_harmonicHomogeneous k j p p.property⟩) : SphereL2) = _
      exact congrArg Subtype.val (harmonicSphereRotation_apply_image (k+1) j i _)
    simp only [Submodule.coe_sum,Submodule.coe_smul]
    simp_rw [hTerm]
    have hImage : (V i : SphereL2) =
        polynomialSphereL2 (sphereDerivativeAdjoint k i p) := by
      dsimp [V]
      rw [harmonicDerivativeAdjoint_apply_image]
      rfl
    have hPolynomial : (∑ j : Fin 3, polynomialSphereL2
        (polynomialRotation j i (sphereDerivativeAdjoint k j p))) =
          -((k : ℝ)+2) • polynomialSphereL2 (sphereDerivativeAdjoint k i p) := by
      have h := congrArg polynomialSphereL2 hPoly
      simpa only [map_sum,neg_mul,← smul_eq_C_mul,map_smul,map_neg,neg_smul] using h
    exact hPolynomial.trans
      (congrArg (fun v : SphereL2 => -((k : ℝ)+2) • v) hImage.symm)
  have hCancel : c*(2*(k : ℝ)+3) = -1 := by
    dsimp [c]
    have hn : 2*(k : ℝ)+3 ≠ 0 := by positivity
    push_cast
    field_simp [hn]
    <;> ring
  simp only [hB,map_smul,← Finset.smul_sum,hRot]
  calc
    -(c • (-((k : ℝ)+2) • V i)) + ((k+1 : ℕ) : ℝ) • (c • V i) =
        (c*(2*(k : ℝ)+3)) • V i := by push_cast; module
    _ = -V i := by
      have hScalar := congrArg (fun t : ℝ => t • V i) hCancel
      exact hScalar.trans (neg_one_smul ℝ (V i))

lemma sphereSobolevAngularCoordinateTransposeL_single
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (i : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    sphereSobolevAngularCoordinateTransposeL hF hO hD s i (sphereSobolevSingleL s k u) =
      sphereSobolevSingleL (s-1) (k+1) (harmonicDerivativeAdjoint hF k i u) := by
  have hUpper (n : ℕ) (v : harmonicSphereSubspace n) :
      (∑ j : Fin 3, harmonicSphereRotation (n+1) j i
        (radialDriftAdjointBlockL hF (EuclideanSpace.single j 1) n v)) -
          ((n+1 : ℕ) : ℝ) • radialDriftAdjointBlockL hF (EuclideanSpace.single i 1) n v =
        harmonicDerivativeAdjoint hF n i v := by
    have h := neg_sum_harmonicSphereRotation_radialDriftAdjointBlock_add_degree hF n v i
    have hNeg := congrArg (fun v : harmonicSphereSubspace (n+1) => -v) h
    simpa only [neg_add,neg_neg,sub_eq_add_neg] using hNeg
  cases k with
  | zero =>
    have hNormal : sphereSobolevAngularCoordinateTransposeL hF hO hD s i
        (sphereSobolevSingleL s 0 u) =
      sphereSobolevSingleL (s-1) 1
        ((∑ j : Fin 3, harmonicSphereRotation 1 j i
          (radialDriftAdjointBlockL hF (EuclideanSpace.single j 1) 0 u)) -
            (1 : ℝ) • radialDriftAdjointBlockL hF (EuclideanSpace.single i 1) 0 u) := by
      simp (config := { instances := true }) only
        [sphereSobolevAngularCoordinateTransposeL,ContinuousLinearMap.add_apply,
          ContinuousLinearMap.neg_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
          sphereSobolevLinearCoordinateMulL_constant,map_neg,sphereSobolevRotationL_single,
          sphereSobolevShiftedDegreeL_single,map_sum,map_sub,map_smul,Nat.zero_add,Nat.cast_one,neg_one_smul,one_smul,smul_neg,Finset.sum_neg_distrib]
      abel
    have hUp := congrArg (sphereSobolevSingleL (s-1) (0+1)) (hUpper 0 u)
    have hUp' : sphereSobolevSingleL (s-1) 1
        ((∑ j : Fin 3, harmonicSphereRotation 1 j i
          (radialDriftAdjointBlockL hF (EuclideanSpace.single j 1) 0 u)) -
            (1 : ℝ) • radialDriftAdjointBlockL hF (EuclideanSpace.single i 1) 0 u) =
        sphereSobolevSingleL (s-1) 1 (harmonicDerivativeAdjoint hF 0 i u) := by
      simpa only [Nat.zero_add,Nat.cast_one] using hUp
    exact hNormal.trans hUp' 
  | succ m =>
    have hNormal : sphereSobolevAngularCoordinateTransposeL hF hO hD s i
        (sphereSobolevSingleL s (m+1) u) =
      sphereSobolevSingleL (s-1) m
        ((∑ j : Fin 3, harmonicSphereRotation m j i
          (radialDriftBlockL hF (EuclideanSpace.single j 1) m u)) -
            (m : ℝ) • radialDriftBlockL hF (EuclideanSpace.single i 1) m u) +
      sphereSobolevSingleL (s-1) (m+2)
        ((∑ j : Fin 3, harmonicSphereRotation (m+2) j i
          (radialDriftAdjointBlockL hF (EuclideanSpace.single j 1) (m+1) u)) -
            ((m+2 : ℕ) : ℝ) • radialDriftAdjointBlockL hF (EuclideanSpace.single i 1) (m+1) u) := by
      simp (config := { instances := true }) only
        [sphereSobolevAngularCoordinateTransposeL,ContinuousLinearMap.add_apply,
          ContinuousLinearMap.neg_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
          sphereSobolevLinearCoordinateMulL_single_succ,map_sub,map_neg,
          sphereSobolevRotationL_single,sphereSobolevShiftedDegreeL_single,
          map_sum,map_smul,Finset.sum_sub_distrib,Finset.sum_neg_distrib,Nat.add_assoc,neg_one_smul,one_smul,smul_neg]
      abel
    have hLowZero :
        (∑ j : Fin 3, harmonicSphereRotation m j i
          (radialDriftBlockL hF (EuclideanSpace.single j 1) m u)) -
            (m : ℝ) • radialDriftBlockL hF (EuclideanSpace.single i 1) m u = 0 :=
      sub_eq_zero.mpr (sum_harmonicSphereRotation_radialDriftBlock hF m u i)
    have hLowImage : sphereSobolevSingleL (s-1) m
        ((∑ j : Fin 3, harmonicSphereRotation m j i
          (radialDriftBlockL hF (EuclideanSpace.single j 1) m u)) -
            (m : ℝ) • radialDriftBlockL hF (EuclideanSpace.single i 1) m u) = 0 := by
      simpa only [map_zero] using congrArg (sphereSobolevSingleL (s-1) m) hLowZero
    have hUpperImage : sphereSobolevSingleL (s-1) (m+2)
        ((∑ j : Fin 3, harmonicSphereRotation (m+2) j i
          (radialDriftAdjointBlockL hF (EuclideanSpace.single j 1) (m+1) u)) -
            ((m+2 : ℕ) : ℝ) • radialDriftAdjointBlockL hF (EuclideanSpace.single i 1) (m+1) u) =
        sphereSobolevSingleL (s-1) (m+2) (harmonicDerivativeAdjoint hF (m+1) i u) := by
      simpa only [Nat.add_assoc] using
        (congrArg (sphereSobolevSingleL (s-1) ((m+1)+1)) (hUpper (m+1) u))
    have hBoth := congrArg₂ (fun a b : SphereSobolev (s-1) => a+b) hLowImage hUpperImage
    exact hNormal.trans (hBoth.trans (zero_add _))

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sum_harmonicSphereRotation_radialDriftBlock
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.neg_sum_harmonicSphereRotation_radialDriftAdjointBlock_add_degree
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevAngularCoordinateTransposeL_single
