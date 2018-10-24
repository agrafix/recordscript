(function(number){var fibRec=(function(index,prev,current){return(((index<=0)?current:fibRec((index-1),(prev+current),prev)));});return(fibRec(number,1,0));})
