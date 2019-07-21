use ff::{Field, PrimeField, PrimeFieldRepr};

#[derive(PrimeField)]
#[PrimeFieldModulus = "41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888458477323173057491593855069696241854796396165721416325350064441470418137846398469611935719059908164220784476160001"]
#[PrimeFieldGenerator = "17"]
pub struct Fr(FrRepr);