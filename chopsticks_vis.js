require('d3')

const stage = new Stage()

/////////////////////////////////////////////////////////////////////
// Handle all states
/////////////////////////////////////////////////////////////////////

// Create a grid object that contains one cell per state
//    `instances` is an array that contains the states

const numTeams = instances[0].signature('Team').atoms().length

const stateGridConfig = {
    grid_location :{
        x:50,
        y:150
    },
    cell_size:{
        x_size:300,
        y_size:100*numTeams
    },
    grid_dimensions:{
        y_size: instances.length,
        x_size:1
    }
  }

const statesGrid = new Grid(stateGridConfig)
// var Y= 100
// For every instance, place a visualization in the proper grid location
instances.forEach( (inst, idx) => {    
    const lb = idx == loopBack ? " (loopback)" : ""
    statesGrid.add({x:0, y:idx}, new TextBox(`State:${idx}${lb}`,{x:0,y:0},'black',16))

    // stage.add(new TextBox({
    //     text: `${numTeams}`, 
    //     coords: {x:300, y:Y},
    //     color: 'black',
    //     fontSize: 16}))
    // Y=Y+100;

    statesGrid.add({x:0, y:idx}, visualizeStateAsText(inst, idx))    
})

/////////////////////////////////////////////////////////////////////
// Handle each individual state
/////////////////////////////////////////////////////////////////////

function visualizeStateAsText(inst, idx) {
    const teams = inst.signature('Team').atoms()
    const hands = [...inst.signature('Team').join(inst.field('hands')).tuples().map(h => h.atoms().map(at => at.id())).flat()]
    const fingers = inst.signature('Hand').atoms().map(h => h.join(inst.field('fingers')).tuples()).flat()
    // Because Hands array from Hand signature is not the same order as the hands array retrieved from Teams' fields, this corrects it: 
    const handsOrder= inst.signature('Hand').tuples().map(h => h.atoms().map(at => at.id())).flat().map(h => hands.indexOf(h))
    const numHandsPerTeam = inst.signature('Team').atoms()[0].join(inst.field('hands')).tuples().length
    
    const lastChangedH1 = inst.signature('Game').join(inst.field('lastChangedH1')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()
    const lastChangedH2 = inst.signature('Game').join(inst.field('lastChangedH2')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()
    const turn = inst.signature('Game').join(inst.field('turn')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()[0]
   
    const group = new Grid({
        grid_location :{
            x:10,
            y:10
        },
        cell_size:{
            x_size:80,
            y_size:80
        },
        grid_dimensions:{
            y_size: teams.length,
            x_size: numHandsPerTeam + 1
        }
      })

      teams.forEach((team, teamIdx) => {
        // Highlight current turn
        if (turn == team.tuples().map(tup => tup.atoms().map(at => at.id()))[0][0]){
                group.add({x: 0, y:teamIdx}, 
                new Rectangle({
                                height: 80,
                                width: 80,
                                color: 'gray',
                                opacity:0.2,
                            }))
        };

        // Add team name
        group.add({x: 0, y:teamIdx}, 
            new TextBox({
                text: `${team.tuples()}`,
                color: 'black',
                fontSize: 16})
        );


        // Populate hand numbers
        [...Array(numHandsPerTeam).keys()].forEach((handIdx) => {

            const handIdxAll = (teamIdx * numHandsPerTeam) + handIdx
            if (lastChangedH1 == hands[handIdxAll]){
                group.add({x: handIdx+1, y:teamIdx}, 
                    new Circle({radius: 10, opacity: 0.2, color: "red"}))
            }

            if (lastChangedH2 == hands[handIdxAll]){
                group.add({x: handIdx+1, y:teamIdx}, 
                    new Circle({radius: 10, opacity: 0.2, color: "blue"}))
            }

            group.add({x: handIdx+1, y:teamIdx}, 
            new TextBox({
                name: "hi",
                text: `${fingers[handsOrder[handIdxAll]]}`,
                color: 'black',
                fontSize: 16})
            )
        })
    })
    return group
}

// Finally, add the grid to the stage and render it:
const start = 40
stage.add(
    new TextBox({
        text: `${"🥢️ Chopsticks 🥢️"}`,
        coords: {x:140, y:start},
        fontSize: 30
    }))

stage.add(
    new TextBox({
        text: `${"A gray box indicates the team whose turn it is."}`,
        coords: {x:150, y:start+30},
        fontSize: 12
    }))
stage.add(
    new TextBox({
        text: `${"A blue dot marks the hand that just attacked/contributed to a split."}`,
        coords: {x:207, y:start+50},
        fontSize: 12
    }))
stage.add(
    new TextBox({
        text: `${"A red dot marks the hand that was just attacked/received from a split."}`,
        coords: {x:215, y:start+70},
        fontSize: 12
    }))
stage.add(
    new TextBox({
        text: `${"In transfers, the dot colors don't matter."}`,
        coords: {x:130, y:start+90},
        fontSize: 12
    }))
stage.add(statesGrid)
stage.render(svg, document)


// const handImages = [
//     "https://i.imgur.com/IkJ7mzl.png",
//     "https://i.imgur.com/r3ywbgS.png",
//     "https://i.imgur.com/9E9CEt6.png",
//     "https://i.imgur.com/jZYaGO6.png",
//     "https://i.imgur.com/yUcBdKe.png"
// ]
// function render_hand(number) {
//     const img = document.createElement('img')
//     img.src = handImages[number]
//     img.style.width = '100%'
//     img.style.height = '15%'
//     img.style.display = 'block'
//     img.style['margin-bottom'] = '10%'
//     return img;
//   }
