$pdf_mode = 4;
$lualatex = 'lualatex --shell-escape --interaction=nonstopmode --synctex=1 %O %S';
$clean_ext = '%R.brf %R.bbl _minted-%R/';
@default_files = ('thesis.tex');