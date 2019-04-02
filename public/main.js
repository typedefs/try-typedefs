// We assume the global 'window.Typedefs' is the Typedefs library.

var exampleTerms =
  [ "(name MyVoid 0)"
  , "(name MyUnit 1)"
  , "; a type variable, indicated by 'var', is represented by its De Bruijn-index" + "\n" +
    "(name MyVar (var 0))" + "\n"
  , "(name MySum (+ 1 0))"
  , "(name MyProduct (* 1 1))"

  , "(name Nat (mu (Zero 1) (Succ (var 0))))"
  , "(name List (mu (Nil 1) (Cons (* (var 1) (var 0)))))"
  , "; for List of Nat, we need type application (TODO)" + "\n" +
    "(name Nat (mu (Zero 1)" + "\n" +
    "              (Succ (var 0))))" + "\n" +
    "" + "\n" +
    "(name List (mu (Nil 1)" + "\n" +
    "               (Cons (* (var 1) (var 0)))))" + "\n"

  , "(name ListNat (mu (NilN 1) (ConsN (* (mu (Z 1) (S (var 1))) (var 0)))))" // now if you wanted to generate `data ListNat = NilN | ConsN Nat Nat ListNat` you'd have to copy/paste the `nat` mu part
  , "(name Maybe (+ 1 (var 0)))"
  , "(name Maybe (mu (Nil 1) (Just (var 1))))"

  , "(name LeBool (mu (LeFalse 1) (LeTrue 1)))"
  , "; 'name' allows for let-binding and aliasing" + "\n" +
    "(name either      (+ (var 0) (var 1)))" + "\n" +
    "(name bit         (+ 1 1))" + "\n" +
    "(name nibble      (* bit bit bit bit))" + "\n" +
    "(name bitOrNibble (either bit nibble))" + "\n"
  ];

// not used atm
function getSourceTextFromUrlBar () {
  var text1 = location.search;
  console.log('getIt: text1 =', text1)
  // console.log('getIt: text1 =', R.dropWhile(x => x != '=', text1))
  // console.log('getIt: text1 =', R.split('=', text1))
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

function getSourceTextFromInput () {
  var inputElem = document.getElementById('input-tdef2')
  var text = inputElem.value
  return text
}

function setSource (text) {
  document.getElementById("input-tdef2").innerHTML = text;
}

function setResult (text_, text2) {
  console.log('setResult: text =', text_)
  let text = (text_ || "").trim()
  document.getElementById("output-haskell").innerHTML = text;
}

function copyExample (exampleSourceCode) {
  console.log('copyExample: exampleSourceCode =', exampleSourceCode)
  setSource(exampleSourceCode);
}

function Idris_foldMaybe (onNothing, onJust, m) {
  return m['type'] == 0 ? onNothing() : onJust(m['$1'])
}

function main () {
  var text = getSourceTextFromInput()
  console.log('main: text =', text)
  setSource(text);

  // TODO replace \n by <br> when rendering an example
  var mkEx = ex => '<a class="navbar-item" href="#"><code onclick="copyExample(this.innerHTML)">' + ex + '</code></a>'
  var exampleMenuItems = R.compose(R.join('\n'), R.map(mkEx))(exampleTerms)
  document.getElementById('js-navbar-examples-dropdown').innerHTML = exampleMenuItems

  var inputElem = document.getElementById('input-tdef2')
  inputElem.focus()
  var butCompile = document.getElementById('compile2')
  function doCompile () {

    var targetLang = document.querySelector('input[data-target-lang]:checked').dataset['targetLang'] || 'json'

    console.log('targetLang =', targetLang)

    var text = getSourceTextFromInput()
    console.log('butCompile clicked: text:', text)
    var astMaybe = Typedefs.parseType(text)
    console.log('astMaybe =', astMaybe)
    var target = Idris_foldMaybe( ()  => 'Parse error.'
                                , ast => Typedefs.generateCode(targetLang, ast)
                                , astMaybe
                                )
    setResult(target)
  }
  butCompile.addEventListener('click', doCompile)

  // TODO examples should be a dictionary, so we can copy by key
  copyExample("(name LeBool (mu (LeFalse 1) (LeTrue 1)))")
  doCompile()
}
