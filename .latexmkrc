$pdf_mode = 4;
$lualatex = 'lualatex --shell-escape --interaction=nonstopmode --synctex=1 %O %S';
$jobname = 'ubc_2022_november_chan_jonathan';
$bibtex_use = 2;
$success_cmd = "latexmk -c";
push @generated_exts, 'brf';
@default_files = ('thesis.tex');