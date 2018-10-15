var exampleTerms =
  [ "(name MyVoid 0)"
  , "(name MyUnit 1)"
  , "(name MyVar (var 0))"
  , "(name MySum (+ 1 0))"
  , "(name MyProduct (* 1 1))"
  , "(mu Nat (Zero 1) (Succ (var 0)))" // TODO errr is nat ok like this?
  , "(mu List (Nil 1) (Cons (* (var 1) (var 0))))"
  , "(mu ListNat (NilN 1) (ConsN (* (mu Nat (Z 1) (S (var 0))) (var 0))))" // now if you wanted to generate `data ListNat = NilN | ConsN Nat Nat ListNat` you'll have to copypaste the `nat` mu part
  , "(name Maybe (+ 1 (var 0)))"
  , "(mu   Maybe (Nil 1) (Just (var 1)))"
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
  var text = inputElem.innerHTML
  return text
}

// currently, this is invoked BY the main function in the Idris JS code!
function getSource () {
  var text = getSourceTextFromInput()
  console.log('getSource: text =', text)
  return text
}

function setSource (text) {
  document.getElementById("input-tdef").innerHTML = text;
  document.getElementById("input-tdef2").innerHTML = text;
}

// currently, this is invoked BY the main function in the Idris JS code!
function setResult (text, text2) {
  console.log('setResult: text =', text)
  document.getElementById("output-haskell").innerHTML = text;
}

function copyExample (exampleSourceCode) {
  console.log('copyExample: exampleSourceCode =', exampleSourceCode)
  setSource(exampleSourceCode);
}

function main () {
  var text = getSourceTextFromInput()
  console.log('main: text =', text)
  setSource(text);

  var mkEx = ex => '<a class="navbar-item" href="#"><code onclick="copyExample(this.innerHTML)">' + ex + '</code></a>'
  var exampleMenuItems = R.compose(R.join('\n'), R.map(mkEx))(exampleTerms)
  document.getElementById('js-navbar-examples-dropdown').innerHTML = exampleMenuItems

  var inputElem = document.getElementById('input-tdef2')
  inputElem.focus()
  var butCompile = document.getElementById('compile2')
  function onClickButCompile (e) {
    var text = getSourceTextFromInput()
    console.log('butCompile clicked: text:', text)
    window.idris_main()
  }
  butCompile.addEventListener('click', onClickButCompile)
}
