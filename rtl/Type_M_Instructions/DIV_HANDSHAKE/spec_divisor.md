  


clock   -> 
  nreset  ->  reset assincrono com nível baixo ativo
  valid   -> Indicação de quando existe um dado válido no barramento
  a       -> Dividendo
  b       -> Divisor
  c       -> Resultado da operação
  nclocks -> Retorna o número de ciclo de clocks da operação 
  ready   -> Indicação de quando o módulo esta apto a iniciar o cálculo solicitado
  done    -> indicação de conclusão da operação


pinout:

clock   - input
nreset  - input
valid   - input
a       - input
b       - input
c       - output
ready   - output
done    - output
