# es/ -- la charla en espanol

**No es una traduccion.** Decidido 2026-08-10, y esto reemplaza por completo el
plan anterior de este archivo, que la describia como una traduccion idiomatica
de `en/main.tex` con el mismo esqueleto de frames.

Es una charla **nueva, general y con limite de tiempo**, para un publico **no
hostil que ha oido hablar de la IA y poco mas**. Su tema no es VNB: es

1. que es un LLM, en terminos accesibles;
2. por que un LLM podria ser un *instrumento* para la investigacion matematica;
3. y, como consecuencia, que justifica el proyecto VNB --- un relato de en que
   se ha empleado el tiempo.

El expositor es hablante nativo, de modo que **se escribe directamente en
espanol**; no hace falta un original en ingles.

## Consecuencias para la construccion

* **`make parity` esta RETIRADO** (2026-08-11). Comparaba los `\fid{...}` de
  `en/main.tex` y `es/main.tex` frame por frame y fallaba si divergian: tenia
  sentido para una traduccion y ninguno para una charla distinta. Los
  marcadores `\fid{...}` siguen en el mazo ingles; no componen nada y siguen
  sirviendo para nombrar un frame cuando los numeros de pagina se han movido.
* **`../shared/` se sigue usando** para lo que aplique: `numbers.tex` (una
  cifra corregida no puede pudrirse aqui mientras es correcta alla), las
  figuras, y el preambulo. Una charla general citara pocas cifras.
* **Los frames tecnicos NO se reciclan sin recortar.** El mazo en ingles es un
  superconjunto de 54 paginas del que una charla selecciona; esta charla
  selecciona muy poco de el.
* **Sin `babel`.** Esta maquina no tiene `texlive-lang-spanish`: no hay
  `spanish.ldf` y `language.dat` solo trae patrones ingleses, de modo que
  `\usepackage[spanish]{babel}` aborta la compilacion. `main.tex` desactiva la
  particion de palabras en su lugar (mejor ninguna que una inglesa, que seria
  incorrecta) y escribe la fecha en espanol a mano. En una maquina con el
  paquete: reponer la linea de babel y borrar el bloque de penalizaciones. La
  cadena UTF-8 (utf8 + T1) funciona tal cual.

## Decision de vocabulario, aun abierta

**`macete`** es **portugues** --- un truco ingenioso, casi un juego de manos ---
y entro en el vocabulario a traves de IMPS. Un publico hispanohablante lo oira
como una casi-palabra y no como un termino tecnico, lo cual corta en las dos
direcciones. Dejarlo sin traducir y glosarlo en su primer uso, o traducirlo.
