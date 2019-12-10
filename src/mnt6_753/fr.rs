use ff::{Field, PrimeField, PrimeFieldRepr};

#[derive(PrimeField)]
#[PrimeFieldModulus = "41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888253786114353726529584385201591605722013126468931404347949840543007986327743462853720628051692141265303114721689601"]
#[PrimeFieldGenerator = "17"]
pub struct Fr(FrRepr);

#[allow(dead_code)]
fn print_repr(name: &str, s: &str) {
    let x = Fr::from_str(s).unwrap();
    match x {
        Fr(FrRepr(a)) => println!(
            "pub const {}: Fr = Fr(FrRepr([{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}]));",
            name, a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11]
        ),
    }
}

#[test]
fn test_constants() {
    print_repr("MINUS_ONE", "41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888253786114353726529584385201591605722013126468931404347949840543007986327743462853720628051692141265303114721689600");
    print_repr("G2_COFACTOR_A", "2767030263454220691701760000");
    print_repr("G2_COFACTOR_B", "15142042904733176096953510025644478161476816537990018683369737365919935002349082421910914002766553024230392501114955454464156014499019476551199810250859823358396362117604489078716851165991537952164920");
    print_repr("G2_COFACTOR_C", "22770455506746448515948239906636514754838761436546571984087972308048800766619956554324392872564144992864755219106229369491103964922688810379557445798014807426645476765843025062178980848099686919638058764203995530073582726125723");
}

// It is computed as 2*(q³ + 1) / r
// COFACTOR = 35109670907775722334885409509333745183738954240640089194284201405607790002339749922481971496467789325719563022803110172775314580383491990543672007441895200462887965706517271013291572878491690838989323590044544644906199056783792700213427458168232
// 18496697809615571808458807494990228873320511733864120944739259385004396846276859845751585270474278624395873989959434393934345835550787006221735852321286149835872779336737936547657953820569411518376528402841604
// AS cofactor is larger than R (because G2 is a cubic twist) => therefore cofactor ~= q²
// We write the cofactor as A*(B(r-1)+C) with
// (a = 2767030263454220691701760000)
// ===================
// (b = 15142042904733176096953510025644478161476816537990018683369737365919935002349082421910914002766553024230392501114955454464156014499019476551199810250859823358396362117604489078716851165991537952164920)
// ===================
// (c = 22770455506746448515948239906636514754838761436546571984087972308048800766619956554324392872564144992864755219106229369491103964922688810379557445798014807426645476765843025062178980848099686919638058764203995530073582726125723)
// ===================
pub const MINUS_ONE: Fr = Fr(FrRepr([
    14260497802974073023,
    5895249896161266456,
    14682908860938702530,
    17222385991615618722,
    14621060510943733448,
    10594887362868996148,
    7477357615964975684,
    12570239403004322603,
    2180620924574446161,
    12129628062772479841,
    8853285699251153944,
    362282887012814,
]));
pub const G2_COFACTOR_A: Fr = Fr(FrRepr([
    11409275485933613416,
    1041003502988525234,
    3592458366775098345,
    10121082542199901504,
    9881285144704759978,
    6713185379730056703,
    17322437275491914718,
    2820261027666504391,
    2829210860663722969,
    7584885545500418020,
    5622284837073779729,
    169349717906506,
]));
pub const G2_COFACTOR_B: Fr = Fr(FrRepr([
    16281489864242660242,
    14605335144557295663,
    7071704294468683453,
    13656764251056669381,
    3209849599740134123,
    9444286556348853291,
    16955538235950066544,
    10768285710560715673,
    4857735338813096880,
    16874308810701960730,
    9717263542993910715,
    246334269261119,
]));
pub const G2_COFACTOR_C: Fr = Fr(FrRepr([
    1456304585306742900,
    1114951049930798527,
    6926128723265006978,
    3712224973817015482,
    14766289582922374778,
    9212442810907195800,
    17098005713221086646,
    405167929502972271,
    16489366854190297035,
    18077948245612198622,
    13412243737376176170,
    28592235364837,
]));