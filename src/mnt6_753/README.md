# MNT6-753

This is an implementation of the MNT6-753 pairing-friendly elliptic curve
construction.

## MNT6 Parameterization

MNT6 curves are parameterized by a value *x* such that the base field modulus
*q* and subgroup *r* can be computed by:

* q = 4x<sup>2</sup> + 1
* r = 4x<sup>2</sup> + 2x + 1

Given primes *q* and *r* parameterized as above, we can easily construct an
elliptic curve over the prime field F<sub>*q*</sub> which contains a subgroup
of order *r* such that *r* | (*q*<sup>6</sup> - 1), giving it an embedding
degree of 6. Instantiating its quartic twist over an extension field
F<sub>q<sup>2</sup></sub> gives rise to an efficient bilinear pairing function
between elements of the order *r* subgroups of either curves, into an order *r*
multiplicative subgroup of F<sub>q<sup>12</sup></sub>.

## MNT6-753 Instantiation

The MNT6 construction is instantiated by `x = something`, which
produces the largest `q` and smallest Hamming weight of `x` that meets the
above requirements. This produces:

* r =
  `mnt6753_modulus_r = bigint_r("41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888253786114353726529584385201591605722013126468931404347949840543007986327743462853720628051692141265303114721689601");
`
= `0x1c4c62d92c41110229022eee2cdadb7f997505b8fafed5eb7e8f96c97d87307fdb925e8a0ed8d99d124d9a15af79db117e776f218059db80f0da5cb537e38685acce9767254a4638810719ac425f0e39d54522cdd119f5e9063de245e8001`

* q = 
  `mnt6753_modulus_q = bigint_q("41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888458477323173057491593855069696241854796396165721416325350064441470418137846398469611935719059908164220784476160001");
`
= `0x1c4c62d92c41110229022eee2cdadb7f997505b8fafed5eb7e8f96c97d87307fdb925e8a0ed8d99d124d9a15af79db26c5c28c859a99b3eebca9429212636b9dff97634993aa4d6c381bc3f0057974ea099170fa13a4fd90776e240000001`


TODO: change this bit :) 

Our extension field tower is constructed as follows:

1. F<sub>q<sup>2</sup></sub> is constructed as F<sub>q</sub>(u) /
(u<sup>2</sup> - β) where β = -1.
2. F<sub>q<sup>6</sup></sub> is constructed as F<sub>q<sup>2</sup></sub>(v) /
(v<sup>3</sup> - ξ) where ξ = u + 1
3. F<sub>q<sup>12</sup></sub> is constructed as F<sub>q<sup>6</sup></sub>(w) /
(w<sup>2</sup> - γ) where γ = v

Now, we instantiate the elliptic curve E(F<sub>q</sub>) : y<sup>2</sup> =
x<sup>3</sup> + 4, and the elliptic curve E'(F<sub>q<sup>2</sup></sub>) :
y<sup>2</sup> = x<sup>3</sup> + 4(u + 1).

The group G<sub>1</sub> is the *r* order subgroup of E, which has cofactor (x -
1)<sup>2</sup> / 3. The group G<sub>2</sub> is the *r* order subgroup of E',
which has cofactor (x<sup>8</sup> - 4x<sup>7</sup> + 5x<sup>6</sup> -
4x<sup>4</sup> + 6x<sup>3</sup> - 4x<sup>2</sup> - 4x + 13) / 9.

### Generators

#### G1
```
mnt6753_G1::G1_one = mnt6753_G1(mnt6753_Fq("16364236387491689444759057944334173579070747473738339749093487337644739228935268157504218078126401066954815152892688541654726829424326599038522503517302466226143788988217410842672857564665527806044250003808514184274233938437290"),
                              mnt6753_Fq("4510127914410645922431074687553594593336087066778984214797709122300210966076979927285161950203037801392624582544098750667549188549761032654706830225743998064330900301346566408501390638273322467173741629353517809979540986561128"),
                              mnt6753_Fq::one());
```

#### G2

```
mnt6753_G2::G2_one = mnt6753_G2(mnt6753_Fq3(mnt6753_Fq("46538297238006280434045879335349383221210789488441126073640895239023832290080310125413049878152095926176013036314720850781686614265244307536450228450615346834324267478485994670716807428718518299710702671895190475661871557310"),
                                       mnt6753_Fq("10329739935427016564561842963551883445915701424214177782911128765230271790215029185795830999583638744119368571742929964793955375930677178544873424392910884024986348059137449389533744851691082159233065444766899262771358355816328"),
                                       mnt6753_Fq("19962817058174334691864015232062671736353756221485896034072814261894530786568591431279230352444205682361463997175937973249929732063490256813101714586199642571344378012210374327764059557816647980334733538226843692316285591005879")),
                              mnt6753_Fq3(mnt6753_Fq("5648166377754359996653513138027891970842739892107427747585228022871109585680076240624013411622970109911154113378703562803827053335040877618934773712021441101121297691389632155906182656254145368668854360318258860716497525179898"),
                                       mnt6753_Fq("26817850356025045630477313828875808893994935265863280918207940412617168254772789578700316551065949899971937475487458539503514034928974530432009759562975983077355912050606509147904958229398389093697494174311832813615564256810453"),
                                       mnt6753_Fq("32332319709358578441696731586704495581796858962594701633932927358040566210788542624963749336109940335257143899293177116050031684054348958813290781394131284657165540476824211295508498842102093219808642563477603392470909217611033")),
                              mnt6753_Fq3::one());
```


## Serialisation 

The most-significant three bits of a G1 or G2 encoding should be masked away
before the coordinate(s) are interpreted. These bits are used to unambiguously
represent the underlying element:

* The most significant bit, when set, indicates that the point is in compressed
  form. Otherwise, the point is in uncompressed form.
* The second-most significant bit indicates that the point is at infinity. If
  this bit is set, the remaining bits of the group element's encoding should be
  set to zero.
* The third-most significant bit is set if (and only if) this point is in
  compressed form _and_ it is not the point at infinity _and_ its y-coordinate
  is the lexicographically largest of the two associated with the encoded
  x-coordinate.
