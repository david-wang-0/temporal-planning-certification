fun zip_with_index xs = 
    ListPair.zip xs (tabulate (List.length xs, (fn i => i)))