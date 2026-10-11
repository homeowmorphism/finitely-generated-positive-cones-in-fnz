module

public import FnZPositiveCones.Interfaces

@[expose] public section

/-! The fixed product-group certificate. All identities are kernel checked. -/
namespace FnZPositiveCones

def productX : FnZ 2 := (FreeGroup.of 0, 1)
def productY : FnZ 2 := (FreeGroup.of 1, 1)
def productZ : FnZ 2 := (1, Multiplicative.ofAdd 1)

def sixAlpha : Fin 6 → FnZ 2 := ![
  productX,
  productY * productX * productZ⁻¹,
  productX⁻¹ * productY * productX * productZ⁻¹,
  productX⁻¹ * productY⁻¹ * productX⁻¹ * productY * productX,
  productX⁻¹ * productY⁻¹ * productZ ^ 2,
  productX⁻¹ * productY⁻¹ * productX * productZ ^ 2]

def sixC : FnZ 2 := productY⁻¹ * productX⁻¹ * productY * productX * productZ⁻¹
def sixBeta (s : Fin 6) : FnZ 2 := if s = 0 then sixC else 1

theorem sixWeightTable_relations (s : Fin 6) :
    sixAlpha s = sixBeta s * sixAlpha (s - 1) * sixAlpha (s + 1) * sixBeta (s + 3) := by
  fin_cases s <;> apply Prod.ext <;>
    norm_num [sixAlpha, sixBeta, sixC, productX, productY, productZ, Fin.reduceSub,
      Fin.reduceAdd, mul_assoc] <;> group

theorem sixWeightTable_Z : sixAlpha 0 * sixAlpha 2 * sixAlpha 4 = productZ := by
  apply Prod.ext <;> norm_num [sixAlpha, productX, productY, productZ, mul_assoc]
  group

theorem sixWeightTable_Y : sixAlpha 0 * sixAlpha 2 ^ 2 * sixAlpha 4 = productY := by
  apply Prod.ext <;> norm_num [sixAlpha, productX, productY, productZ, pow_two, mul_assoc]

end FnZPositiveCones
