/*

- latex export
- command line export voor jelle (zie de dir ./parser)
- meer terpjes via alex
- let-bindings?

- Just eraf pellen: Just (0 ** (1 + 1))
  - kan evt met een JS hackje
- ook die ** sigma afpellen: Just (0 ** (1 + 1))

- exposen JS API
  - ook haskell backend: generate, generateType

- TName defs?
  - voorbeeld van eentje die parseert?
  - TODO oh das mss omdat ik een te oude JS typedefs bundle gebruik :/
- definities die naar elkaar verwijzen?
- een lijst van tdef expressies parsen?

- waarom is de structuur van showTDef anders dan de haskell backend?

- doet TermCodec al iets?

- MathJax?
*/

// TODO (name ) overal omheen ivm haskell gen
var exampleTerms =
  [ "(name MyVoid 0)"
  , "(name MyUnit 1)"
  , "(name MyVar (var 0))"
  , "name MySum (+ 1 0))"
  , "name MyProduct (* 1 1))"
  // , "(name (var 1)"
  // , "(name (var 123)"

  , "(mu Nat (Zero 1) (Succ (var 0)))" // TODO errr is nat ok like this?
  , "(mu List (Nil 1) (Cons (* (var 1) (var 0))))"
  , "(mu ListNat (NilN 1) (ConsN (* (mu Nat (Z 1) (S (var 0))) (var 0))))" // now if you wanted to generate `data ListNat = NilN | ConsN Nat Nat ListNat` you'll have to copypaste the `nat` mu part
  , "(name Maybe (+ 1 (var 0)))"
  , "(mu   Maybe (Nil 1) (Just (var 1)))"
  // , "(+ 1 (* (var 0) 0))"
  // , "(+ 1 1 0)"
  // , "(+ 1 1 0 (* 1 0))"
  ];

function getIt1 () {
  var text1 = location.search;
  console.log('getIt: text1 =', text1)
  console.log('getIt: text1 =', R.dropWhile(x => x != '=', text1))
  console.log('getIt: text1 =', R.split('=', text1))
  var text2 = R.split('=', text1)[1] // TODO [1] is a brittle way of extracting the value for the key 'input-tdef'
  console.log('getIt: text2 =', text2)
  var text3 = decodeURI(text2)
  console.log('getIt: text3 =', text3)

  // console.log('getIt: unescape(text2) =', unescape(text2))
  // console.log('getIt: decodeURIComponent(text2) =', decodeURIComponent(text2))


  var text4 = text2.replace(/[+]/g, ' ')
  console.log('getIt: text4 =', text4)

  var text5 = decodeURI(text4)
  console.log('getIt: text5 =', text5)

  var text6 = unescape(text5)
  console.log('getIt: text6 =', text6)

  return text6
}

function getIt2 () {
  var input2 = document.getElementById('input-tdef2')
  var text = input2.innerHTML
  //console.log('getIt2: input2 =', input2)
  console.log('getIt2: text =', text)
  return text
}

// currently, this is invoked BY the main function in the Idris JS code!
function getSource () {
  var text3 = getIt2()
  console.log('getSource: text3 =', text3)
  return text3
}

function setSource (text) {
  document.getElementById("input-tdef").innerHTML = text;
}

// currently, this is invoked BY the main function in the Idris JS code!
function setResult (text, text2) {
  console.log('setResult: text =', text)
  console.log('setResult: text2 =', text2)
  document.getElementById("output-tdef").innerHTML = text;
  document.getElementById("output-haskell").innerHTML = text;
}

function main () {
  var text0 = getIt2()
  console.log('main: text0 =', text0)
  setSource(text0);

  // document.getElementById('examples').innerHTML = '<h1>Examples</h1><ul>' + R.compose(R.join('\n'), R.map(ex => '<li><code>' + ex + '</code></li>'))(exampleTerms) + '</ul>'
  var mkEx = ex => '<a class="navbar-item" href="#"><code>' + ex + '</code></a>'
  var exampleMenuItems = R.compose(R.join('\n'), R.map(mkEx))(exampleTerms)
  document.getElementById('js-navbar-examples-dropdown').innerHTML = exampleMenuItems


  var input2 = document.getElementById('input-tdef2')
  input2.focus()
  var but2 = document.getElementById('compile2')
  function onClickBut2 (e) {
    var text = getIt2() // input2.innerHTML
    console.log('but2 clicked: ', text)
    window.idris_main()
  }
  but2.addEventListener('click', onClickBut2)

}
