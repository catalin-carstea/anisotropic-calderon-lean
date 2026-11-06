import Calderon.ActualFullEPhysicalEndpoints

/-! Typed cubic mixed-word transpose difference; auxiliary algebra only.
Full before-source proof is cubic-pairing-upfront-v001/UPFRONT.md.
No actual lower estimate, extra final premise or acceptance is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCubicPairing
variable {Hi Half Neg Phys ι : Type*}
  [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Half] [NormedSpace ℝ Half]
  [NormedAddCommGroup Neg] [NormedSpace ℝ Neg]
  [NormedAddCommGroup Phys] [InnerProductSpace ℝ Phys]

/-- The four gain terms place the first input only through the downward inclusion. -/
theorem cubic_pairing_sub_transpose_eq_four_pairings
    (I : Hi →L[ℝ] Half) (J : Half →L[ℝ] Neg) (K : Half →L[ℝ] Phys)
    (PP : Half →L[ℝ] Neg →L[ℝ] ℝ)
    (A B : ι → Hi →L[ℝ] Half) (AL BL : ι → Half →L[ℝ] Neg)
    (G : ι → ι → Hi →L[ℝ] Half) (Cl : ι → ι → Half →L[ℝ] Neg)
    (hA : ∀ a x, J (A a x) = AL a (I x))
    (hB : ∀ a x, J (B a x) = BL a (I x))
    (hPivot : ∀ a x y, PP x (AL a y) = PP y (BL a x))
    (hPair : ∀ x z, PP x (J z) = ⟪K x, K z⟫_ℝ)
    (hG : ∀ a b x, J (G a b x) = BL a (A b x)-AL b (B a x))
    (hCl : ∀ a b x, Cl a b (I x) = J (G a b x))
    (hClPivot : ∀ a b x y, PP x (Cl a b y) = PP y (Cl b a x))
    (a b c : ι) (v w : Hi) :
    (PP (A a v) (AL b (A c w))+PP (B a v) (BL c (B b w)))-
      (PP (A a w) (AL b (A c v))+PP (B a w) (BL c (B b v))) =
      PP (I v) (Cl a b (A c w))+PP (I v) (AL b (G a c w))-
      PP (I v) (Cl c a (B b w))-PP (I v) (BL c (G b a w)) := by
  have hSym (x z : Half) : PP x (J z) = PP z (J x) := by
    rw [hPair, hPair, real_inner_comm]
  have hMoveA (s : ι) (x : Hi) (z : Half) :
      PP (A s x) (J z) = PP (I x) (BL s z) := by
    calc
      _ = PP z (J (A s x)) := hSym _ _
      _ = PP z (AL s (I x)) := congrArg (PP z) (hA s x)
      _ = _ := hPivot s z (I x)
  have hMoveB (s : ι) (x : Hi) (z : Half) :
      PP (B s x) (J z) = PP (I x) (AL s z) := by
    calc
      _ = PP z (J (B s x)) := hSym _ _
      _ = PP z (BL s (I x)) := congrArg (PP z) (hB s x)
      _ = _ := (hPivot s (I x) z).symm
  have hRow (s t : ι) (x : Hi) :
      BL s (A t x) = J (G s t x)+AL t (B s x) := by
    rw [hG s t x]
    abel
  have hT (x y : Hi) :
      PP (A a x) (AL b (A c y))-PP (B a y) (BL c (B b x)) =
        PP (A c y) (J (G b a x))+PP (B b x) (J (G a c y)) := by
    have he : PP (A a x) (AL b (A c y)) =
        PP (A c y) (J (G b a x))+PP (B b x) (J (G a c y))+
          PP (B a y) (BL c (B b x)) := by
      calc
        _ = PP (A c y) (BL b (A a x)) := hPivot b _ _
        _ = PP (A c y) (J (G b a x))+PP (A c y) (AL a (B b x)) := by
          rw [hRow b a x, map_add]
        _ = PP (A c y) (J (G b a x))+PP (B b x) (BL a (A c y)) := by
          rw [hPivot a (A c y) (B b x)]
        _ = PP (A c y) (J (G b a x))+
            (PP (B b x) (J (G a c y))+PP (B b x) (AL c (B a y))) := by
          rw [hRow a c y, map_add]
        _ = _ := by rw [hPivot c (B b x) (B a y)]; ring
    linarith only [he]
  have hMoveC (s t : ι) (z : Half) (x : Hi) :
      PP z (J (G s t x)) = PP (I x) (Cl t s z) := by
    calc
      _ = PP z (Cl s t (I x)) := congrArg (PP z) (hCl s t x).symm
      _ = _ := hClPivot s t z (I x)
  have hvw := hT v w
  have hwv := hT w v
  rw [hMoveC b a (A c w) v, hMoveB b v (G a c w)] at hvw
  rw [hMoveA c v (G b a w), hMoveC a c (B b w) v] at hwv
  linarith only [hvw, hwv]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCubicPairing
