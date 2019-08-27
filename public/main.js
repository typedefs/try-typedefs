// We assume the global 'window.Typedefs' is the Typedefs library.

var exampleTerms =
  [ "; Booleans correspond to a sum of unit types." + "\n" +
    "(name Bool (+ 1 1))"

  , "; The Maybe or Option data type is formed as a sum of Unit and a type variable." + "\n" +
    "; Type variables, indicated by 'var', are represented by their De Bruijn-indices." + "\n" +
    "(name Maybe (+ 1 (var 0)))"

  , "; Bool can also be formed using 'mu', using its named constructors." + "\n" +
    "(name Bool (mu (F 1) (T 1)))"

  , "; An alternative definition of Maybe via 'mu'." + "\n" +
    "; There is no recursion because (var 1) is not self-referential, unlike (var 0)." + "\n" +
    "(name Maybe (mu (Nothing 1)" + "\n" +
    "                (Just (var 1))))" + "\n"

  , "; Basic data types like Bit and Byte are defined from scratch." + "\n" +
    "(name Either      (+ (var 0) (var 1)))" + "\n" +
    "(name Bit         (+ 1 1))" + "\n" +
    "(name Byte        (* Bit Bit Bit Bit Bit Bit Bit Bit))" + "\n" +
    "(name BitOrByte   (Either Bit Byte))" + "\n"

  , "; An inductive definition of the natural numbers." + "\n" +
    "; The (var 0) type variable makes the mu-expression refer to itself" + "\n" +
    "(name Nat (mu (Zero 1)" + "\n" +
    "              (Succ (var 0))))"

  , "; List are defined inductively, like Nat." + "\n" +
    "; However, they contain an additional term of type (var 1)." + "\n" +
    "(name List (mu (Nil 1)" + "\n" +
    "               (Cons (* (var 1) (var 0)))))" + "\n"

  , "; To form List of Nat, we need type application (TODO)" + "\n" +
    "(name Nat (mu (Zero 1)" + "\n" +
    "              (Succ (var 0))))" + "\n" +
    "" + "\n" +
    "(name List (mu (Nil 1)" + "\n" +
    "               (Cons (* (var 1) (var 0)))))" + "\n"

  , "; We can still form List of Nat without type application directly:" + "\n" +
    "(name ListNat (mu (NilN 1)" + "\n" +
    "              (ConsN (* (mu (Z 1) (S (var 1))) (var 0)))))"

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

function getTargetLang () {
  return document.querySelector('input[data-target-lang]:checked')
                 .dataset['targetLang'] || 'json'
}

function doCompile () {
  var targetLang = getTargetLang()
  console.log('targetLang =', targetLang)

  var textWithComments = getSourceTextFromInput()
  console.log('doCompile: textWithComments:\n', textWithComments)
  var text = stripComments(textWithComments)
  console.log('doCompile: text:\n', text)
  // $1 exploits the fact that Either values are always placed in $1 and in this case both 
  // branches of the Either return strings
  var generated = Typedefs.generateTermSerializers(targetLang, text).$1
  console.log('generated =', generated)
  setResult(generated)
}

function exampleHtml (ex) {
  return '<a class="navbar-item" href="#"><pre onclick="copyExample(this.innerHTML)">' +
         ex +
         '</pre></a>'
}

function stripComments (s) {
  var stripCommentLine = R.replace(/\s*[;].+$/gm, '')
  var stripEmptyLine = R.replace(/^\s*[\r\n]/gm, '')
  return R.compose(stripCommentLine, stripEmptyLine)(s)
}

function main () {
  var text = getSourceTextFromInput()
  console.log('main: text =', text)
  setSource(text);

  // TODO replace \n by <br> when rendering an example
  var exampleMenuItems = R.compose(R.join('\n'), R.map(exampleHtml))(exampleTerms)
  document.getElementById('js-navbar-examples-dropdown').innerHTML = exampleMenuItems

  var inputElem = document.getElementById('input-tdef2')
  inputElem.focus()

  var butCompile = document.getElementById('compile2')
  butCompile.addEventListener('click', doCompile)

  // TODO examples should be a dictionary, so we can copy by key
  copyExample(exampleTerms[0])
  doCompile()
}
