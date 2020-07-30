

This is an attempt to make use of [Booij 2020 - Analysis in Univalent Type Theory](https://abooij.blogspot.com/p/phd-thesis.html) to get a _cauchy-complete archimedean field_ into `--cubical` Agda as [suggested in a Github issue](https://github.com/agda/cubical/issues/286). I am quite verbosely copying from [chapter 4](chapter-4-1.md) of Booij's thesis.

$\int_\Omega f\,\mathrm{d}x$


<!--

Bonus trick: to hide an Agda code block, just put it between html comments

<pre class="Agda"><a id="477" class="Symbol">{-#</a> <a id="481" class="Keyword">OPTIONS</a> <a id="489" class="Pragma">--cubical</a> <a id="499" class="Pragma">--no-import-sorts</a> <a id="517" class="Pragma">--allow-unsolved-metas</a> <a id="540" class="Symbol">#-}</a>
<a id="544" class="Comment">-- need --allow-unsolved-metas for generating html</a>
<a id="595" class="Comment">--   see https://github.com/agda/agda/issues/3642</a>
</pre>
-->

The "main" file is 


<pre class="Agda"><a id="681" class="Keyword">import</a> <a id="688" href="SyntheticReals.html" class="Module">SyntheticReals</a>
</pre>
extensions of `Cubical.Foundations.Logic` and similar things live in

<pre class="Agda"><a id="782" class="Keyword">import</a> <a id="789" href="MoreLogic.html" class="Module">MoreLogic</a>
</pre>