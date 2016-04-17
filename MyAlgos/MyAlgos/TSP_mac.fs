//////// Travelling Salesman problem ////////


open System
open System.Collections
open System.Collections.Generic
open System.IO

open System.Windows

// open FSharp.Charting

//open MyLibrary
//open MyLibrary.MyUsefulFunctions
//open MyLibrary.MyCollections

exception InnerError of string


let stopWatch = System.Diagnostics.Stopwatch.StartNew()
let stopWatch1 = System.Diagnostics.Stopwatch.StartNew()

///////////////// preparing the data /////////////////

// format of the files
//[number_of_cities]
//[x_1] [y_1] // coordinate

// original MOOC file with 25 cities
let x = File.ReadAllLines "/Users/francois-guillaume.rideau/Documents/MOOC/TSP.txt"
// answer = 26442.7
// path=[|0y; 4y; 7y; 3y; 2y; 6y; 8y; 12y; 13y; 15y; 23y; 24y; 19y; 16y; 20y; 22y; 21y;
//  17y; 18y; 14y; 11y; 10y; 9y; 5y; 1y; 0y|]





// test sample file with 18 cities from MOOC forum
// let x = File.ReadAllLines "/Users/francois-guillaume.rideau/Documents/MOOC/TSP_test18.txt"
// TSP answer = (12, 3.50115585f)
// path=[|0y; 12y; 6y; 11y; 3y; 17y; 14y; 8y; 5y; 15y; 10y; 1y; 7y; 2y; 9y; 16y; 4y; 13y;
//  0y|]
// very fast

let split (text:string)=
    text.Split [|'\t';' '|]

let splitInto2Values (A: string []) =  
    (float A.[0],float A.[1])

let parseLine (line:string) = 
    line
    |> split 
    |> splitInto2Values
 


let num_cities = int x.[0] // 25
let cities = x |> Array.tail |> Array.map parseLine //  [x_1][y_1] 

// square
// let num_cities=4
// let cities = [|(0.0,0.0);(0.0,1.0);(1.0,0.0);(1.0,1.0)|] 

// linear path
// let num_cities =4
// let cities = [|(0.0,0.0);(0.0,2.0);(0.0,4.0);(0.0,6.0)|] 

// rectangular path
// let num_cities =10
// let cities = [|(0.0,0.0);(0.0,1.0);(0.0,2.0);(0.0,3.0);(0.0,4.0);(1.0,4.0);(1.0,3.0);(1.0,2.0);(1.0,1.0);(1.0,0.0)|] 








let dist_matrix = Array2D.create num_cities num_cities 0.0f
for i in 0..(num_cities-1)do
    for j in 0..(num_cities-1) do
        dist_matrix.[i,j]<- float32 (sqrt  ( (fst cities.[i] - fst cities.[j])*(fst cities.[i] - fst cities.[j]) + (snd cities.[i] - snd cities.[j])*(snd cities.[i] - snd cities.[j]) ))

let arrayOfArrays = [| [| 0.0f; 2.0f;1.0f;4.0f |]; [|2.0f;0.0f; 3.0f;5.0f |]; [|1.0f;3.0f; 0.0f;6.0f |]; [|4.0f;5.0f; 6.0f;0.0f |] |]
let example = Array2D.init 4 4 (fun i j -> arrayOfArrays.[i].[j]) 

//let a = Bitwise.power2 3
//let b = Search.mini [(1,1);(2,3);(3,0)]

// make a plot
// in F# interactive
// let C = Chart.Point (Array.toList cities)
// C.ChartShow()


////////////////////////////////////

// Dynamic programming algorithm

// Subproblems: 
// For every destination j in {1,2,......n} every subset S in {1,2,....n} that contains 1 and j, let
// A(S,j) = minimum length of a path of a path from 1 to j that visits precisely the vertices of S [exactly once each]

// create A = Array2D indexed by subsets S that contain 1 and destinations j
// Base Case A[S,1] = 0 if S = {1} , +infinity otherwise
// for m = 2,3,4,.... n (m = subproblem size)
//     for each Set S in {1,2,...n} of size m that contains 1
//         for each j in S, j different from 1:
//             A[S,j] = min (k in S, k <> j) {A[S-{j},k]+Ckj}
// Return min (j=2 to n) A[{1,2,3,....,n},j]+Cj1


let limit = 100000000.0f


let TSP_all_c_Dynamic_Programming(D:float32 [,]) = // solves the TSP problem when ALL cities are connected together with an exhaustive search in exponential time O(n^2 2^n)
                                                   // the input is a distance matrix in float32
                                                   // memory usage is not optimized at all....   
    let num_cities = Array2D.length1 D
    let l2 = Array2D.length2 D
    if (l2<>num_cities) then failwith "Distance matrix is not a squared matrix"
    let powers_of_2 = [|1;2;4;8;16;32;64;128;256;512;1024;2048;4096;8192;16384;32768;65536;131072;262144;524288;1048576;2097152;4194304;8388608;16777216|]
    let power2 k =    
       if ((k >= 25) || (k<0)) then raise (InnerError("power exponent not allowed"))
           else powers_of_2.[k]  

    let num_subsets = power2 (num_cities-1)
    let S_full = num_subsets-1 

    let A = Array2D.create num_subsets (num_cities-1)  limit
    
    A.[0,0]<-0.0f
    
    let rec sumbits (n:int):int=
      let rec helper acc m =
         match m with
            | 0 -> acc
            | 1 -> acc+1 // enlever cela ?
            | _ -> let r = m%2
                   helper (acc+r) (m>>>1)
      helper 0 n

    let hashtable = Array2D.create (num_cities-1) num_subsets false // hashtable.[i-1,n]=true if (sumbits n) = i
    for k in 1..(num_subsets-1) do hashtable.[(sumbits k)-1,k]<-true
    // member returns [(p,2^p);....] if the pth city is in S
    let members S = [for j in 0..(num_cities-2) do let a= powers_of_2.[j] &&& S
                                                   if (a<>0) then yield (j,a)] // list length = num_cities-1

    for m in 2..num_cities do // on fixe la taille de S
        printfn "m=%A" m
        let mutable count = 0
        let stopWatch = System.Diagnostics.Stopwatch.StartNew()

        let Subset_of_size_m = hashtable.[m-2,0..] |> Seq.mapi (fun i x -> (i,x)) |> Seq.filter (fun (a,b)-> (b=true)) |> Seq.map fst |> Seq.toList
        for S in Subset_of_size_m do         
            if m = 2 then let (i,S') = (members S).Head
                          A.[S',i]<- D.[0,i+1] // distance from 0 to city i+1
                     else
                          let S'_list = List.fold (fun acc x -> let a = (((snd x)^^^S_full)&&&S)             // list of subsets of size m-1
                                                                if a = S then acc else (fst x,a)::acc ) [] (members S)
                          for (j,S') in S'_list do
                              A.[S,j] <- ([for (k,expk) in (members S') do
                                                yield A.[S',k]+D.[j+1,k+1]] |> List.min) // can do better than that if we remember from above
            count <- count + 1
            if count%10000=0 then printfn "count=%A" count                 
        printfn "%f" stopWatch.Elapsed.TotalMilliseconds

    printfn "%A" A
    A.[num_subsets-1,0..]

/// run that sub

// let A = TSP_all_c_Dynamic_Programming dist_matrix

// let res = [for i in 0..num_cities-2 do yield (A.[i]+ dist_matrix.[0,i+1]) ]  |> Seq.mapi (fun i x -> (i, x)) |> Seq.minBy snd
// printfn "TSP answer = %A" res
// Console.ReadKey() |> ignore

//
//
/////////////////////////////// with path ////////////////////////////////////////////




let TSP_all_c_Dynamic_Programming_with_path_main(D:float32 [,]) = // solves the TSP problem when ALL cities are connected together with an exhaustive search in exponential time O(n^2 2^n)
                                                   // the input is a distance matrix in float32
                                                   // memory usage is not optimized at all....   
    let num_cities = Array2D.length1 D
    let l2 = Array2D.length2 D
    if (l2<>num_cities) then failwith "Distance matrix is not a squared matrix"
    let powers_of_2 = [|1;2;4;8;16;32;64;128;256;512;1024;2048;4096;8192;16384;32768;65536;131072;262144;524288;1048576;2097152;4194304;8388608;16777216|]
    let power2 k =    
       if ((k >= 25) || (k<0)) then raise (InnerError("power exponent not allowed"))
           else powers_of_2.[k]  

    let num_subsets = power2 (num_cities-1)
    let S_full = num_subsets-1 

    let dyn_res = new Dictionary<int,float32 []>() // stores dynamically results // key = S ; value = (dyn_res.[S]).[j]=A[S,j])
    let predecessor = Array2D.create num_subsets (num_cities-1) -1y

    let Dict_Add_or_Insert (dict:Dictionary<int,float32 []>) ((k,(j,v)):int*(int*float32)) =

         if  dict.ContainsKey k = false then dict.Add (k,Array.create (num_cities-1) limit)
                                             (dict.[k]).[j] <- v
                                        else (dict.[k]).[j] <- v

    Dict_Add_or_Insert dyn_res (0,(0,0.0f))
    
    let rec sumbits (n:int):int=
      let rec helper acc m =
         match m with
            | 0 -> acc
            | 1 -> acc+1 // enlever cela ?
            | _ -> let r = m%2
                   helper (acc+r) (m>>>1)
      helper 0 n

    // build the subsets of fixed size m thanks to a hashtable
    let hashtable = Array2D.create (num_cities-1) num_subsets false // hashtable.[i-1,n]=true if (sumbits n) = i
    for k in 1..(num_subsets-1) do hashtable.[(sumbits k)-1,k]<-true


    // let subsets_by_size : (int list) [] = Array.create (num_cities-1) [] // this method takes more memory
    // for k in 1..(num_subsets-1) do subsets_by_size.[(sumbits k)-1]<- k::subsets_by_size.[(sumbits k)-1] 

    // member returns [(p,2^p);....] if the pth city is in S
    let members S = [for j in 0..(num_cities-2) do let a= powers_of_2.[j] &&& S
                                                   if (a<>0) then yield (j,a)] // list length = num_cities-1

    
    // m=2 done manually //

    for i in 0..num_cities-2 do
        let S = powers_of_2.[i]
        Dict_Add_or_Insert dyn_res (S,(i,D.[0,i+1])) // distance from 0 to city i+1
        predecessor.[S,i] <- -1y


    let mutable old_Subset = hashtable.[0,0..] |> Seq.mapi (fun i x -> (i,x)) |> Seq.filter (fun (a,b)-> (b=true)) |> Seq.map fst |> Seq.toList

    for m in 3..num_cities do // on fixe la taille de S
        printfn "m=%A" m
        let stopWatch = System.Diagnostics.Stopwatch.StartNew()

        let mutable count = 1

        let Subset_of_size_m = hashtable.[m-2,0..] |> Seq.mapi (fun i x -> (i,x)) |> Seq.filter (fun (a,b)-> (b=true)) |> Seq.map fst |> Seq.toList
        // let Subset_of_size_m = subsets_by_size.[m-2]

        for S in Subset_of_size_m do         

                          let S'_list = List.fold (fun acc x -> let a = (((snd x)^^^S_full)&&&S)             // list of subsets of size m-1 included in S
                                                                if a = S then acc else (fst x,a)::acc ) [] (members S)
                          for (j,S') in S'_list do
                              let (tmp1,tmp2) = ([for (k,expk) in (members S') do
                                                       yield ((dyn_res.[S']).[k]+D.[j+1,k+1],k) ]|> List.min |> fun (a,b)->(a,sbyte b))// can do better than that if we remember from above
                              Dict_Add_or_Insert dyn_res (S,(j,tmp1))
                              predecessor.[S,j] <- tmp2

                          // printfn "S=%A %A" S dyn_res.[S]
             
                          // count <- count + 1
                          // if count%10000 =0 then printfn "count=%A" count

        // when the iteration is over, we can delete non relevant entries
        // if (m>=3) then for S' in subsets_by_size.[m-3] do (dyn_res.Remove S' |> ignore)

        // can optimize code by storing Subset_of_size_m-1
        // if (m>=3) then for S' in (hashtable.[m-3,0..] |> Seq.mapi (fun i x -> (i,x)) |> Seq.filter (fun (a,b)-> (b=true)) |> Seq.map fst |> Seq.toList) do (dyn_res.Remove S' |> ignore)
        if (m>=3) then for S' in old_Subset do (dyn_res.Remove S' |> ignore)
        old_Subset <- Subset_of_size_m
        printfn "%f" stopWatch.Elapsed.TotalMilliseconds

    printfn "Sfull = %A" dyn_res.[S_full]
    (dyn_res.[S_full],predecessor)

let calculate_path_TSP_all_c_Dynamic_Programming_with_path (D:float32 [,]) =
    
    let (A,predecessor) = TSP_all_c_Dynamic_Programming_with_path_main D
                                                    // memory usage is not optimized at all....   
    let num_cities = Array2D.length1 D
    let l2 = Array2D.length2 D
    if (l2<>num_cities) then failwith "Distance matrix is not a squared matrix"

    let powers_of_2 = [|1;2;4;8;16;32;64;128;256;512;1024;2048;4096;8192;16384;32768;65536;131072;262144;524288;1048576;2097152;4194304;8388608;16777216|]
    let power2 k =    
       if ((k >= 25) || (k<0)) then raise (InnerError("power exponent not allowed"))
           else powers_of_2.[k]  

    let num_subsets = power2 (num_cities-1)
    let S_full = num_subsets-1 


    let res' = [for i in 0..num_cities-2 do yield (A.[i]+ D.[0,i+1]) ]  |> Seq.mapi (fun i x -> (i, x)) |> Seq.minBy snd
    printfn "TSP answer = %A" res'

    let path = Array.create (num_cities+1) -1y

    let mutable current_city = sbyte (fst res')
    path.[num_cities-1]<- current_city// the last city 

    let mutable current_S = S_full
    let mutable next_S = -2
    let mutable next_city = -2y

    for k in num_cities-2..-1..1 do 
        next_city <- predecessor.[current_S,int current_city]
        next_S <- (S_full^^^powers_of_2.[int current_city]) &&& current_S
        //printfn "k=%A current_S=%A next_city=%A" k current_S next_city
        path.[k]<-next_city
        current_S<-next_S
        current_city<-next_city

    for i in 0..num_cities do path.[i]<-path.[i]+1y
    printfn "path=%A" path  


////// main program /////
printfn "TSP with path"
calculate_path_TSP_all_c_Dynamic_Programming_with_path dist_matrix
printfn "%f" stopWatch1.Elapsed.TotalMilliseconds
