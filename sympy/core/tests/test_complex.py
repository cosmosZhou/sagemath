from sympy import (S, Symbol, sqrt, I, Integer, Rational, cos, sin, im, re, Abs,
        exp, sinh, cosh, tan, tanh, conjugate, sign, cot, coth, pi, symbols,
        expand_complex)


def test_complex():
    a = Symbol("a", real=True)
    b = Symbol("b", real=True)
    e = (a + I*b)*(a - I*b)
    assert e.expand() == a**2 + b**2
    assert sqrt(I) == sqrt(I)


def test_conjugate():
    a = Symbol("a", real=True)
    b = Symbol("b", real=True)
    c = Symbol("c", imaginary=True)
    d = Symbol("d", imaginary=True)
    x = Symbol('x')
    z = a + I*b + c + I*d
    zc = a - I*b - c + I*d
    assert conjugate(z) == zc
    assert conjugate(exp(z)) == exp(zc)
    assert conjugate(exp(I*x)) == exp(-I*conjugate(x))
    assert conjugate(z**5) == zc**5
    assert conjugate(abs(x)) == abs(x)
    assert conjugate(sign(z)) == sign(zc)
    assert conjugate(sin(z)) == sin(zc)
    assert conjugate(cos(z)) == cos(zc)
    assert conjugate(tan(z)) == tan(zc)
    assert conjugate(cot(z)) == cot(zc)
    assert conjugate(sinh(z)) == sinh(zc)
    assert conjugate(cosh(z)) == cosh(zc)
    assert conjugate(tanh(z)) == tanh(zc)
    assert conjugate(coth(z)) == coth(zc)


def test_abs1():
    a = Symbol("a", real=True)
    b = Symbol("b", real=True)
    assert abs(a) == abs(a)
    assert abs(-a) == abs(a)
    assert abs(a + I*b) == sqrt(a**2 + b**2)


def test_abs2():
    a = Symbol("a", real=False)
    b = Symbol("b", real=False)
    assert abs(a) != a
    assert abs(-a) != a
    assert abs(a + I*b) != sqrt(a**2 + b**2)


def test_evalc():
    x = Symbol("x", real=True)
    y = Symbol("y", real=True)
    z = Symbol("z")
    assert ((x + I*y)**2).expand(complex=True) == x**2 + 2*I*x*y - y**2
    assert expand_complex(z**(2*I)) == (re((re(z) + I*im(z))**(2*I)) +
        I*im((re(z) + I*im(z))**(2*I)))
    assert expand_complex(
        z**(2*I), deep=False) == I*im(z**(2*I)) + re(z**(2*I))

    assert exp(I*x) != cos(x) + I*sin(x)
    assert exp(I*x).expand(complex=True) == cos(x) + I*sin(x)
    assert exp(I*x + y).expand(complex=True) == exp(y)*cos(x) + I*sin(x)*exp(y)

    assert sin(I*x).expand(complex=True) == I * sinh(x)
    assert sin(x + I*y).expand(complex=True) == sin(x)*cosh(y) + \
        I * sinh(y) * cos(x)

    assert cos(I*x).expand(complex=True) == cosh(x)
    assert cos(x + I*y).expand(complex=True) == cos(x)*cosh(y) - \
        I * sinh(y) * sin(x)

    assert tan(I*x).expand(complex=True) == tanh(x) * I
    assert tan(x + I*y).expand(complex=True) == (
        sin(2*x)/(cos(2*x) + cosh(2*y)) +
        I*sinh(2*y)/(cos(2*x) + cosh(2*y)))

    assert sinh(I*x).expand(complex=True) == I * sin(x)
    assert sinh(x + I*y).expand(complex=True) == sinh(x)*cos(y) + \
        I * sin(y) * cosh(x)

    assert cosh(I*x).expand(complex=True) == cos(x)
    assert cosh(x + I*y).expand(complex=True) == cosh(x)*cos(y) + \
        I * sin(y) * sinh(x)

    assert tanh(I*x).expand(complex=True) == tan(x) * I
    assert tanh(x + I*y).expand(complex=True) == (
        (sinh(x)*cosh(x) + I*cos(y)*sin(y)) /
        (sinh(x)**2 + cos(y)**2)).expand()


def test_pythoncomplex():
    x = Symbol("x")
    assert 4j*x != 4*x*I
    assert 4j*x == 4.0*x*I
    assert 4.1j*x != 4*x*I


def test_rootcomplex():
    R = Rational
    assert ((+1 + I)**R(1, 2)).expand(
        complex=True) == 2**R(1, 4)*cos(  pi/8) + 2**R(1, 4)*sin(  pi/8)*I
    assert ((-1 - I)**R(1, 2)).expand(
        complex=True) == 2**R(1, 4)*cos(3*pi/8) - 2**R(1, 4)*sin(3*pi/8)*I
    assert (sqrt(-10)*I).as_real_imag() == (-sqrt(10), 0)


def test_expand_inverse():
    assert (1/(1 + I)).expand(complex=True) == (1 - I)/2
    assert ((1 + 2*I)**(-2)).expand(complex=True) == (-3 - 4*I)/25
    assert ((1 + I)**(-8)).expand(complex=True) == Rational(1, 16)


def test_expand_complex():
    assert ((2 + 3*I)**10).expand(complex=True) == -341525 - 145668*I
    # the following two tests are to ensure the SymPy uses an efficient
    # algorithm for calculating powers of complex numbers. They should execute
    # in something like 0.01s.
    assert ((2 + 3*I)**1000).expand(complex=True) == \
        -81079464736246615951519029367296227340216902563389546989376269312984127074385455204551402940331021387412262494620336565547972162814110386834027871072723273110439771695255662375718498785908345629702081336606863762777939617745464755635193139022811989314881997210583159045854968310911252660312523907616129080027594310008539817935736331124833163907518549408018652090650537035647520296539436440394920287688149200763245475036722326561143851304795139005599209239350981457301460233967137708519975586996623552182807311159141501424576682074392689622074945519232029999 + \
        46938745946789557590804551905243206242164799136976022474337918748798900569942573265747576032611189047943842446167719177749107138603040963603119861476016947257034472364028585381714774667326478071264878108114128915685688115488744955550920239128462489496563930809677159214598114273887061533057125164518549173898349061972857446844052995037423459472376202251620778517659247970283904820245958198842631651569984310559418135975795868314764489884749573052997832686979294085577689571149679540256349988338406458116270429842222666345146926395233040564229555893248370000*I
    assert ((2 + 3*I/4)**1000).expand(complex=True) == \
        Integer(1)*37079892761199059751745775382463070250205990218394308874593455293485167797989691280095867197640410033222367257278387021789651672598831503296531725827158233077451476545928116965316544607115843772405184272449644892857783761260737279675075819921259597776770965829089907990486964515784097181964312256560561065607846661496055417619388874421218472707497847700629822858068783288579581649321248495739224020822198695759609598745114438265083593711851665996586461937988748911532242908776883696631067311443171682974330675406616373422505939887984366289623091300746049101284856530270685577940283077888955692921951247230006346681086274961362500646889925803654263491848309446197554307105991537357310209426736453173441104334496173618419659521888945605315751089087820455852582920963561495787655250624781448951403353654348109893478206364632640344111022531861683064175862889459084900614967785405977231549003280842218501570429860550379522498497412180001/114813069527425452423283320117768198402231770208869520047764273682576626139237031385665948631650626991844596463898746277344711896086305533142593135616665318539129989145312280000688779148240044871428926990063486244781615463646388363947317026040466353970904996558162398808944629605623311649536164221970332681344168908984458505602379484807914058900934776500429002716706625830522008132236281291761267883317206598995396418127021779858404042159853183251540889433902091920554957783589672039160081957216630582755380425583726015528348786419432054508915275783882625175435528800822842770817965453762184851149029376 + \
        I*421638390580169706973991429333213477486930178424989246669892530737775352519112934278994501272111385966211392610029433824534634841747911783746811994443436271013377059560245191441549885048056920190833693041257216263519792201852046825443439142932464031501882145407459174948712992271510309541474392303461939389368955986650538525895866713074543004916049550090364398070215427272240155060576252568700906004691224321432509053286859100920489253598392100207663785243368195857086816912514025693453058403158416856847185079684216151337200057494966741268925263085619240941610301610538225414050394612058339070756009433535451561664522479191267503989904464718368605684297071150902631208673621618217106272361061676184840810762902463998065947687814692402219182668782278472952758690939877465065070481351343206840649517150634973307937551168752642148704904383991876969408056379195860410677814566225456558230131911142229028179902418223009651437985670625/1793954211366022694113801876840128100034871409513586250746316776290259783425578615401030447369541046747571819748417910583511123376348523955353017744010395602173906080395504375010762174191250701116076984219741972574712741619474818186676828531882286780795390571221287481389759837587864244524002565968286448146002639202882164150037179450123657170327105882819203167448541028601906377066191895183769810676831353109303069033234715310287563158747705988305326397404720186258671215368588625611876280581509852855552819149745718992630449787803625851701801184123166018366180137512856918294030710215034138299203584
    assert ((2 + 3*I)**-1000).expand(complex=True) == \
        Integer(1)*-81079464736246615951519029367296227340216902563389546989376269312984127074385455204551402940331021387412262494620336565547972162814110386834027871072723273110439771695255662375718498785908345629702081336606863762777939617745464755635193139022811989314881997210583159045854968310911252660312523907616129080027594310008539817935736331124833163907518549408018652090650537035647520296539436440394920287688149200763245475036722326561143851304795139005599209239350981457301460233967137708519975586996623552182807311159141501424576682074392689622074945519232029999/8777125472973511649630750050295188683351430110097915876250894978429797369155961290321829625004920141758416719066805645579710744290541337680113772670040386863849283653078324415471816788604945889094925784900885812724984087843737442111926413818245854362613018058774368703971604921858023116665586358870612944209398056562604561248859926344335598822815885851096698226775053153403320782439987679978321289537645645163767251396759519805603090332694449553371530571613352311006350058217982509738362083094920649452123351717366337410243853659113315547584871655479914439219520157174729130746351059075207407866012574386726064196992865627149566238044625779078186624347183905913357718850537058578084932880569701242598663149911276357125355850792073635533676541250531086757377369962506979378337216411188347761901006460813413505861461267545723590468627854202034450569581626648934062198718362303420281555886394558137408159453103395918783625713213314350531051312551733021627153081075080140680608080529736975658786227362251632725009435866547613598753584705455955419696609282059191031962604169242974038517575645939316377801594539335940001 - Integer(1)*46938745946789557590804551905243206242164799136976022474337918748798900569942573265747576032611189047943842446167719177749107138603040963603119861476016947257034472364028585381714774667326478071264878108114128915685688115488744955550920239128462489496563930809677159214598114273887061533057125164518549173898349061972857446844052995037423459472376202251620778517659247970283904820245958198842631651569984310559418135975795868314764489884749573052997832686979294085577689571149679540256349988338406458116270429842222666345146926395233040564229555893248370000*I/8777125472973511649630750050295188683351430110097915876250894978429797369155961290321829625004920141758416719066805645579710744290541337680113772670040386863849283653078324415471816788604945889094925784900885812724984087843737442111926413818245854362613018058774368703971604921858023116665586358870612944209398056562604561248859926344335598822815885851096698226775053153403320782439987679978321289537645645163767251396759519805603090332694449553371530571613352311006350058217982509738362083094920649452123351717366337410243853659113315547584871655479914439219520157174729130746351059075207407866012574386726064196992865627149566238044625779078186624347183905913357718850537058578084932880569701242598663149911276357125355850792073635533676541250531086757377369962506979378337216411188347761901006460813413505861461267545723590468627854202034450569581626648934062198718362303420281555886394558137408159453103395918783625713213314350531051312551733021627153081075080140680608080529736975658786227362251632725009435866547613598753584705455955419696609282059191031962604169242974038517575645939316377801594539335940001
    assert ((2 + 3*I/4)**-1000).expand(complex=True) == \
        Integer(1)*4257256305661027385394552848555894604806501409793288342610746813288539790051927148781268212212078237301273165351052934681382567968787279534591114913777456610214738290619922068269909423637926549603264174216950025398244509039145410016404821694746262142525173737175066432954496592560621330313807235750500564940782099283410261748370262433487444897446779072067625787246390824312580440138770014838135245148574339248259670887549732495841810961088930810608893772914812838358159009303794863047635845688453859317690488124382253918725010358589723156019888846606295866740117645571396817375322724096486161308083462637370825829567578309445855481578518239186117686659177284332344643124760453112513611749309168470605289172320376911472635805822082051716625171429727162039621902266619821870482519063133136820085579315127038372190224739238686708451840610064871885616258831386810233957438253532027049148030157164346719204500373766157143311767338973363806106967439378604898250533766359989107510507493549529158818602327525235240510049484816090584478644771183158342479140194633579061295740839490629457435283873180259847394582069479062820225159699506175855369539201399183443253793905149785994830358114153241481884290274629611529758663543080724574566578220908907477622643689220814376054314972190402285121776593824615083669045183404206291739005554569305329760211752815718335731118664756831942466773261465213581616104242113894521054475516019456867271362053692785300826523328020796670205463390909136593859765912483565093461468865534470710132881677639651348709376/2103100954337624833663208713697737151593634525061637972297915388685604042449504336765884978184588688426595940401280828953096857809292320006227881797146858511436638446932833617514351442216409828605662238790280753075176269765767010004889778647709740770757817960711900340755635772183674511158570690702969774966791073165467918123298694584729211212414462628433370481195120564586361368504153395406845170075275051749019600057116719726628746724489572189061061036426955163696859127711110719502594479795200686212257570291758725259007379710596548777812659422174199194837355646482046783616494013289495563083118517507178847555801163089723056310287760875135196081975602765511153122381201303871673391366630940702817360340900568748719988954847590748960761446218262344767250783946365392689256634180417145926390656439421745644011831124277463643383712803287985472471755648426749842410972650924240795946699346613614779460399530274263580007672855851663196114585312432954432654691485867618908420370875753749297487803461900447407917655296784879220450937110470920633595689721819488638484547259978337741496090602390463594556401615298457456112485536498177883358587125449801777718900375736758266215245325999241624148841915093787519330809347240990363802360596034171167818310322276373120180985148650099673289383722502488957717848531612020897298448601714154586319660314294591620415272119454982220034319689607295960162971300417552364254983071768070124456169427638371140064235083443242844616326538396503937972586505546495649094344512270582463639152160238137952390380581401171977159154009407415523525096743009110916334144716516647041176989758534635251844947906038080852185583742296318878233394998111078843229681030277039104786225656992262073797524057992347971177720807155842376332851559276430280477639539393920006008737472164850104411971830120295750221200029811143140323763349636629725073624360001 - Integer(1)*3098214262599218784594285246258841485430681674561917573155883806818465520660668045042109232930382494608383663464454841313154390741655282039877410154577448327874989496074260116195788919037407420625081798124301494353693248757853222257918294662198297114746822817460991242508743651430439120439020484502408313310689912381846149597061657483084652685283853595100434135149479564507015504022249330340259111426799121454516345905101620532787348293877485702600390665276070250119465888154331218827342488849948540687659846652377277250614246402784754153678374932540789808703029043827352976139228402417432199779415751301480406673762521987999573209628597459357964214510139892316208670927074795773830798600837815329291912002136924506221066071242281626618211060464126372574400100990746934953437169840312584285942093951405864225230033279614235191326102697164613004299868695519642598882914862568516635347204441042798206770888274175592401790040170576311989738272102077819127459014286741435419468254146418098278519775722104890854275995510700298782146199325790002255362719776098816136732897323406228294203133323296591166026338391813696715894870956511298793595675308998014158717167429941371979636895553724830981754579086664608880698350866487717403917070872269853194118364230971216854931998642990452908852258008095741042117326241406479532880476938937997238098399302185675832474590293188864060116934035867037219176916416481757918864533515526389079998129329045569609325290897577497835388451456680707076072624629697883854217331728051953671643278797380171857920000*I/2103100954337624833663208713697737151593634525061637972297915388685604042449504336765884978184588688426595940401280828953096857809292320006227881797146858511436638446932833617514351442216409828605662238790280753075176269765767010004889778647709740770757817960711900340755635772183674511158570690702969774966791073165467918123298694584729211212414462628433370481195120564586361368504153395406845170075275051749019600057116719726628746724489572189061061036426955163696859127711110719502594479795200686212257570291758725259007379710596548777812659422174199194837355646482046783616494013289495563083118517507178847555801163089723056310287760875135196081975602765511153122381201303871673391366630940702817360340900568748719988954847590748960761446218262344767250783946365392689256634180417145926390656439421745644011831124277463643383712803287985472471755648426749842410972650924240795946699346613614779460399530274263580007672855851663196114585312432954432654691485867618908420370875753749297487803461900447407917655296784879220450937110470920633595689721819488638484547259978337741496090602390463594556401615298457456112485536498177883358587125449801777718900375736758266215245325999241624148841915093787519330809347240990363802360596034171167818310322276373120180985148650099673289383722502488957717848531612020897298448601714154586319660314294591620415272119454982220034319689607295960162971300417552364254983071768070124456169427638371140064235083443242844616326538396503937972586505546495649094344512270582463639152160238137952390380581401171977159154009407415523525096743009110916334144716516647041176989758534635251844947906038080852185583742296318878233394998111078843229681030277039104786225656992262073797524057992347971177720807155842376332851559276430280477639539393920006008737472164850104411971830120295750221200029811143140323763349636629725073624360001

    a = Symbol('a', real=True)
    b = Symbol('b', real=True)
    assert exp(a*(2 + I*b)).expand(complex=True) == \
        I*exp(2*a)*sin(a*b) + exp(2*a)*cos(a*b)


def test_expand():
    f = (16 - 2*sqrt(29))**2
    assert f.expand() == 372 - 64*sqrt(29)
    f = (Integer(1)/2 + I/2)**10
    assert f.expand() == I/32
    f = (Integer(1)/2 + I)**10
    assert f.expand() == Integer(237)/1024 - 779*I/256


def test_re_im1652():
    x = Symbol('x')
    assert re(x) == re(conjugate(x))
    assert im(x) == - im(conjugate(x))
    assert im(x)*re(conjugate(x)) + im(conjugate(x)) * re(x) == 0


def test_issue_5084():
    x = Symbol('x')
    assert ((x + x*I)/(1 + I)).as_real_imag() == (re((x + I*x)/(1 + I)
            ), im((x + I*x)/(1 + I)))


def test_issue_5236():
    assert (cos(1 + I)**3).as_real_imag() == (-3*sin(1)**2*sinh(1)**2*cos(1)*cosh(1) +
        cos(1)**3*cosh(1)**3, -3*cos(1)**2*cosh(1)**2*sin(1)*sinh(1) + sin(1)**3*sinh(1)**3)


def test_real_imag():
    x, y, z = symbols('x, y, z')
    X, Y, Z = symbols('X, Y, Z', commutative=False)
    a = Symbol('a', real=True)
    assert (2*a*x).as_real_imag() == (2*a*re(x), 2*a*im(x))

    # issue 5395:
    assert (x*x.conjugate()).as_real_imag() == (Abs(x)**2, 0)
    assert im(x*x.conjugate()) == 0
    assert im(x*y.conjugate()*z*y) == im(x*z)*Abs(y)**2
    assert im(x*y.conjugate()*x*y) == im(x**2)*Abs(y)**2
    assert im(Z*y.conjugate()*X*y) == im(Z*X)*Abs(y)**2
    assert im(X*X.conjugate()) == im(X*X.conjugate(), evaluate=False)
    assert (sin(x)*sin(x).conjugate()).as_real_imag() == \
        (Abs(sin(x))**2, 0)

    # issue 6573:
    assert (x**2).as_real_imag() == (re(x)**2 - im(x)**2, 2*re(x)*im(x))

    # issue 6428:
    r = Symbol('r', real=True)
    i = Symbol('i', imaginary=True)
    assert (i*r*x).as_real_imag() == (I*i*r*im(x), -I*i*r*re(x))
    assert (i*r*x*(y + 2)).as_real_imag() == (
        I*i*r*(re(y) + 2)*im(x) + I*i*r*re(x)*im(y),
        -I*i*r*(re(y) + 2)*re(x) + I*i*r*im(x)*im(y))

    # issue 7106:
    assert ((1 + I)/(1 - I)).as_real_imag() == (0, 1)
    assert ((1 + 2*I)*(1 + 3*I)).as_real_imag() == (-5, 5)


def test_pow_issue_1724():
    e = ((-1)**(S(1)/3))
    assert e.conjugate().n() == e.n().conjugate()
    e = S('-2/3 - (-29/54 + sqrt(93)/18)**(1/3) - 1/(9*(-29/54 + sqrt(93)/18)**(1/3))')
    assert e.conjugate().n() == e.n().conjugate()
    e = 2**I
    assert e.conjugate().n() == e.n().conjugate()


def test_issue_5429():
    assert sqrt(I).conjugate() != sqrt(I)

def test_issue_4124():
    from sympy import oo
    assert expand_complex(I*oo) == oo*I

def test_issue_11518():
    x = Symbol("x", real=True)
    y = Symbol("y", real=True)
    r = sqrt(x**2 + y**2)
    assert conjugate(r) == r
    s = abs(x + I * y)
    assert conjugate(s) == r
